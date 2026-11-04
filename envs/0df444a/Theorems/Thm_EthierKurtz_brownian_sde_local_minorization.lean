-- Prove2me | Theorems.Thm_EthierKurtz_brownian_sde_local_minorization
-- name    : EthierKurtz.brownian_sde_local_minorization
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T23:03:35.841988+00:00
-- url     : https://prove2.me/theorems/7bf0b111-88b6-4df2-ae19-81331a6bce92
-- title:
--   Local minorization of the time-T laws of two solutions of a locally nondegenerate Brownian SDE started at nearby points
-- statement:
--   Let $X^x, X^y$ solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$ on the same standard Brownian motion $W$ with $X_0=x$, resp. $X_0=y$, where $\sigma_0,b_0$ are continuous. Assume: (i) for every $R\in\mathbb N$ there are continuous, globally bounded and globally Lipschitz $s_1^R,b_1^R$ equal to $\sigma_0,b_0$ on the ball $\{|z|\le R+3\}$; (ii) on a bounded set $N$ the coefficients agree with continuous $s_2,b_2$ bounded by $S$ and $L$-Lipschitz on all of $\mathbb R^d$, and the averaged diffusion $v\mapsto\tfrac12(s_2(p_1)+s_2(p_2))v$ has a jointly measurable right inverse $J(p,\cdot)$ with $|J(p,v)|\le\Lambda|v|$ (uniform nondegeneracy); (iii) a measurable $B_x\subseteq N$ contains the $2\delta$-neighbourhood of the segment $[x,y]$, $|x-y|^2\le G$, $TS\le\delta/2$, and the explicit smallness condition hsmall (Chebyshev bound for leaving the neighbourhood, Gronwall tracking bound, and the Girsanov/KL cost $(\Lambda^2 G e^{c T}/(2T)+1)/a$) is $\le 1/4$. Then for every set $F\subseteq\mathbb R^d$,
--
--   $$e^{-a}\Big(\mathbb P\big(X^x_T\in \operatorname{int}F\big)-\tfrac14\Big)\le \mathbb P\big(X^y_T\in F\big).$$
--
--   Role: the quantitative minorization (Doeblin-type lower bound) form of the local overlap; a set that the solution from $x$ hits with probability above $1/4$ is hit from $y$ with probability bounded below, which is what reachability arguments (positive probability of entering an open set from every interior point) need, unlike the total-variation form whose bound is not uniform in the target set.
--
--   **Formalization Note**: the interior of $F$ appears on the left because the Girsanov coupling only steers the Euler chain into an open neighbourhood; no measurability of $F$ is assumed (probabilities are real-valued outer measures via `Measure.real`).
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Lemma 3.6 in the Appendix (p. 32: the transition probabilities of a nondegenerate diffusion started in a compact set K overlap, P(t,x,B) >= m_{K,D}(B)); quantitative form by the standard Girsanov coupling with a steering drift and Pinsker/KL bound: M. Hairer, J. C. Mattingly, M. Scheutzow, Asymptotic coupling and a general form of Harris' theorem with applications to stochastic delay equations, Probab. Theory Related Fields 149 (2011) 223-259, https://doi.org/10.1007/s00440-009-0250-6, Section 2 (total variation bound from a Girsanov change of measure)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem brownian_sde_local_minorization {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ : ℕ → SDEState d → SDEDiffusion d} {b₁ : ℕ → SDEState d → SDEState d} {S₁ L₁ : ℕ → ℝ}
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL₁ : ∀ R, 0 ≤ L₁ R)
    (hSg₁ : ∀ R x, ‖s₁ R x‖ ≤ S₁ R ∧ ‖b₁ R x‖ ≤ S₁ R)
    (hLg₁ : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L₁ R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L₁ R * ‖x - y‖)
    (hag₁ : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {s₂ : SDEState d → SDEDiffusion d} {b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, WithLp.toLp 2 (fun i => ∑ j, (s₂ p.1 (i, j) + s₂ p.2 (i, j)) / 2 * J p v j) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, σ₀ x = s₂ x ∧ b₀ x = b₂ x)
    {R₀ : ℝ} (hNR : ∀ x ∈ N, ‖x‖ ≤ R₀) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (hsmall : 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) +
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 +
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a ≤ 1 / 4)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} - 1 / 4) ≤ P.real {ω | Xy T ω ∈ F} := by sorry

end EthierKurtz
