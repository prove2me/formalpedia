-- Prove2me | Theorems.Thm_EthierKurtz_euler_scheme_approx_fd
-- name    : EthierKurtz.euler_scheme_approx_fd
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T18:48:48.176012+00:00
-- url     : https://prove2.me/theorems/48cb9421-1cd0-428d-ac7a-8616471ae099
-- title:
--   Euler-scheme approximation of the finite-dimensional laws of a locally Lipschitz SDE, up to exit probabilities
-- statement:
--   Let $X$ solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=x_0$, and let $s_1,b_1$ be globally bounded, globally $L$-Lipschitz and equal to $\sigma_0,b_0$ on $\bar B_{R+3}$. Let $h_n\downarrow 0$, let $T_1,\dots,T_r\ge 0$ and $j_{i,n}\ge 1$ with $j_{i,n}h_n\le T_i\le (j_{i,n}+1)h_n$, and let $Z^n_k$ be the Euler scheme with step $h_n$ whose coefficients are interpolated linearly between the two last grid values (recursion hZs, $Z^n_{-1}=Z^n_0=x_0$). Then for functions $\varphi_n$ of $r$ pairs that are uniformly bounded ($\le K$) and uniformly $\Lambda$-Lipschitz for the sum of the $2r$ distances, and every $\eta>0$, eventually
--
--   $$\Big|\mathbb E\,\varphi_n\big((Z^n_{j_{i,n}-1},Z^n_{j_{i,n}})_{i\le r}\big)-\mathbb E\,\varphi_n\big((X_{T_i},X_{T_i})_{i\le r}\big)\Big|\le 2K\sum_{i\le r}\mathbb P\big(\exists s\le T_i:\ |X_s|>R\big)+\eta .$$
--
--   Role: the finite-dimensional (several fixed times) version of the Euler approximation, through which the multi-time Markov identity is transferred from the (exactly Markov) scheme to the SDE solution; it is needed for the Markov property of the path after a fixed time.
--
--   **Formalization Note**: the scheme carries the pair (previous, current) grid value; its coefficients are linear in time on each step so that the integrands are continuous. The scheme is driven by the same Brownian motion as $X$ (strong approximation), which is what makes the joint law at several times converge.
-- source:
--   P. E. Kloeden, E. Platen, Numerical Solution of Stochastic Differential Equations, Springer 1992, https://doi.org/10.1007/978-3-662-12616-5, Section 14.1, Theorem 14.1.5 (weak convergence of the Euler scheme) and Section 10.2, Theorem 10.2.2 (strong convergence, which gives convergence of the joint law at finitely many times); D. J. Higham, X. Mao, A. M. Stuart, Strong convergence of Euler-type methods for nonlinear stochastic differential equations, SIAM J. Numer. Anal. 40 (2002) 1041-1063, https://doi.org/10.1137/S0036142901389530, Theorem 2.2 (locally Lipschitz coefficients, localization)

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

theorem euler_scheme_approx_fd {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0))
    {r : ℕ} (T : Fin r → ℝ≥0) (j : Fin r → ℕ → ℕ)
    (hj : ∀ i n, 1 ≤ j i n ∧ (j i n : ℝ) * hn n ≤ T i ∧ (T i : ℝ) ≤ j i n * hn n + hn n)
    (φ : ℕ → (Fin r → SDEState d × SDEState d) → ℝ) {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hφK : ∀ n v, |φ n v| ≤ K)
    (hφL : ∀ n (v v' : Fin r → SDEState d × SDEState d),
      |φ n v - φ n v'| ≤ Λ * ∑ i, (‖(v i).1 - (v' i).1‖ + ‖(v i).2 - (v' i).2‖))
    {η : ℝ} (hη : 0 < η)
    (Z : ℕ → Ω → ℕ → SDEState d × SDEState d) (hZ0 : ∀ n ω, Z n ω 0 = (x₀, x₀))
    (hZs : ∀ n ω (k : ℕ), Z n ω (k + 1) = ((Z n ω k).2, (Z n ω k).2 + WithLp.toLp 2 fun i =>
      (∑ j', (s₁ (Z n ω k).1 (i, j') * (W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
          W ((k : ℝ) * hn n).toNNReal ω j') +
        (s₁ (Z n ω k).2 (i, j') - s₁ (Z n ω k).1 (i, j')) / hn n *
          (hn n * W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
            ∫ v in ((k : ℝ) * hn n)..((k : ℝ) * hn n + hn n), W v.toNNReal ω j'))) +
      b₁ (Z n ω k).1 i * hn n + (b₁ (Z n ω k).2 i - b₁ (Z n ω k).1 i) * hn n ^ 2 / (2 * hn n))) :
    ∀ᶠ n in atTop, |∫ ω, φ n (fun i => Z n ω (j i n)) ∂P -
        ∫ ω, φ n (fun i => (X (T i) ω, X (T i) ω)) ∂P| ≤
      2 * K * ∑ i, (P {ω | ∀ s ≤ T i, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by sorry

end EthierKurtz
