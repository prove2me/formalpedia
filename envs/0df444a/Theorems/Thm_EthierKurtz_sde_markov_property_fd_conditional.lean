-- Prove2me | Theorems.Thm_EthierKurtz_sde_markov_property_fd_conditional
-- name    : EthierKurtz.sde_markov_property_fd_conditional
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T18:01:55.628275+00:00
-- url     : https://prove2.me/theorems/69af4a61-cdfd-415e-ac5a-49d5b2896cb2
-- title:
--   Conditional finite-dimensional Markov property of SDE solutions with locally Lipschitz coefficients, tested against bounded Lipschitz functions of finitely many past and future times
-- statement:
--   Let $X^y$ ($y\in D$) solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=y$, with continuous $\sigma_0,b_0$ that agree on $\bar B_{R+3}$ with globally bounded, globally Lipschitz $s_1^R,b_1^R$ for every $R\in\mathbb N$. Let $t_1,\dots,t_r\ge 0$ and let $F:(\mathbb R^d)^r\to\mathbb R$ be measurable with $|F|\le K$ and $|F(v)-F(v')|\le L_F\sum_{i\le r}|v_i-v_i'|$. Then there is a measurable $g$, $|g|\le K$, with $g(y)=\mathbb E\,F(X^y_{t_1},\dots,X^y_{t_r})$ for $y\in D$ such that for every $x\in D$ and $s\ge 0$ with $X^x_s\in D$ a.s., all past times $0<u_1,\dots,u_q\le s$ and every bounded Lipschitz $G:(\mathbb R^d)^q\to\mathbb R$,
--
--   $$\mathbb E\big[G(X^x_{u_1},\dots,X^x_{u_q})\,F(X^x_{s+t_1},\dots,X^x_{s+t_r})\big]=\mathbb E\big[G(X^x_{u_1},\dots,X^x_{u_q})\,g(X^x_s)\big].$$
--
--   Role: this is the Markov property $\mathbb E[F(X_{s+t_\cdot})\mid\mathcal F_s]=g(X_s)$ tested against the finite-dimensional functionals of the past; with a monotone class argument it identifies the conditional law of the path after time $s$ given the past as the path law started from $X_s$, which the classification theorem needs for the martingale convergence of $\mathbb P(E\mid\mathcal F_s)$ on shift-invariant path events.
--
--   **Formalization Note**: $q=0$ ($G$ constant) is the unconditional finite-dimensional Markov property; the past times are taken strictly positive (at time $0$ the solution is the deterministic starting point).
-- source:
--   X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood 2007, https://doi.org/10.1533/9780857099402, Theorem 2.9.3 (Markov property of solutions: E[f(X_{s+t}) | F_s] = (P_t f)(X_s), applied iteratively at the times s+t_1 < ... < s+t_r and tested against bounded functions of X_{u_1},...,X_{u_q}, u_j <= s); S. N. Ethier, T. G. Kurtz, Markov Processes: Characterization and Convergence, Wiley 1986, https://doi.org/10.1002/9780470316658, Chapter 4, Section 1, Proposition 1.6 (finite-dimensional distributions of a Markov process)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem sde_markov_property_fd_conditional {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    {r : ℕ} (t : Fin r → ℝ≥0) {F : (Fin r → SDEState d) → ℝ}
    (hF : Measurable F) {K Lf : ℝ} (hFK : ∀ v, |F v| ≤ K) (hLf : 0 ≤ Lf)
    (hFL : ∀ v v', |F v - F v'| ≤ Lf * ∑ i, ‖v i - v' i‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, F (fun i => X y (t i) ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∀ (q : ℕ) (u : Fin q → ℝ≥0), (∀ j, 0 < u j ∧ u j ≤ s) →
        ∀ (G : (Fin q → SDEState d) → ℝ), Measurable G → ∀ (KG LG : ℝ), (∀ v, |G v| ≤ KG) →
          0 ≤ LG → (∀ v v', |G v - G v'| ≤ LG * ∑ j, ‖v j - v' j‖) →
          ∫ ω, G (fun j => X x (u j) ω) * F (fun i => X x (s + t i) ω) ∂P =
            ∫ ω, G (fun j => X x (u j) ω) * g (X x s ω) ∂P := by sorry

end EthierKurtz
