-- Prove2me | Theorems.Thm_EDPMBandit_delta1_bound
-- name    : EDPMBandit.delta1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:45.819279+00:00
-- url     : https://prove2.me/theorems/896eb968-400a-413e-b123-32b021f61508
-- title:
--   Proof of Theorem 3, the $\delta_1$ display — $\mathbb E|\delta_1|\le\frac12\beta\mathbb E\|\hat F^\pi_T-F^\pi_T\|^2\le\frac{3\beta K^2\log KT}{2\upsilon T}$
-- statement:
--   Assume Requirement 2 of stability (parameter $\upsilon$), that $U$ is smooth with $M_0=\infty$ and parameter $\beta\ge0$ with differentials $\partial U(F)$, $F\in D^\Delta$, and the standing measurability assumption. Let $\pi$ be an admissible policy and $K,T$ with $\log(KT)\ge3$. With
--
--   $$
--   \delta_1=U(\hat F^\pi_T)-U(F^\pi_T)-\partial U(F^\pi_T)\cdot(\hat F^\pi_T-F^\pi_T),
--   $$
--
--   we have
--
--   $$
--   \mathbb E|\delta_1|\le\frac12\beta\,\mathbb E\big[\|\hat F^\pi_T-F^\pi_T\|^2\big]\le\frac{3\beta K^2\log KT}{2\upsilon T}.
--   $$
--
--   This is the second-order part of the horizon-gap bound of Theorem 3.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - generalization: inside Theorem 3: U stable (both requirements) and smooth → Requirement 2 of stability and smoothness; reason: the display uses only smoothness and Lemma 6, which needs Requirement 2 alone
--   - reading: standing assumption (p.5): the expectations exist and are finite → MeasurableAlongEmp: x ↦ U(G + c·F̂_t(x)) and x ↦ ‖G + c·F̂_t(x)‖ are Borel measurable for all t, G, c; reason: makes every expectation the paper writes the integral of a measurable function; finiteness follows from stability
--   - reading: Theorem 3 holds for T ≥ T₀ (not made explicit for this display) → log KT ≥ 3; reason: the display applies the first part of Lemma 6, whose hypothesis this is
--   - encoding: E[|δ₁| 1{‖F̂^π_T − F^π_T‖ ≤ M₀}] with M₀ = ∞; ∂U(F^π_T) → E|δ₁|; a choice dU F of the differential at every F ∈ D^Δ, applied at F^π_T; reason: with M₀ = ∞ the indicator is 1; the differentials are unique
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.25, proof of Theorem 3, display bounding E[|δ₁| 1{‖F̂^π_T − F^π_T‖ ≤ M₀}] (δ₁ defined in the decomposition above it)

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Proof of Theorem 3, the `δ₁` display (case `M₀ = ∞`), Cassel–Mannor–Zeevi,
arXiv:1806.01380v3, p.25: "For E|δ₁|, recalling the parameter M₀ in Definition 2 (smoothness), we
use smoothness together with the first part of Lemma 6 to get that
E[|δ₁| 𝟙{‖F̂^π_T − F^π_T‖ ≤ M₀}] ≤ ½ β E[‖F̂^π_T − F^π_T‖²] ≤ 3βK² log KT/(2υT)", where (p.25)
`δ₁ = U(F̂^π_T) − U(F^π_T) − ∂U(F^π_T)·(F̂^π_T − F^π_T)`.

**Formalization Note.** With `M₀ = ∞` the indicator is `1`. Smoothness with `M₀ = ∞` is given
as a choice `dU F` of the differential at every `F ∈ D^Δ` (`IsDifferentialAt`), evaluated at the
random point `F^π_T ∈ D^Δ`. Hypotheses: Requirement 2 of stability, smoothness, the standing
measurability assumption of p.5, and `log KT ≥ 3` (the hypothesis of Lemma 6, which the display
uses). Both inequalities are stated. -/
theorem delta1_bound {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (υ β : ℝ)
    (hReq2 : StabilityReq2 S N M υ) (hβ : 0 ≤ β) (dU : S.L → S.L →ₗ[ℝ] ℝ)
    (hdU : ∀ F ∈ mixtures S M, IsDifferentialAt S N U β F (dU F))
    (hmeas : MeasurableAlongEmp S N U) (π : Policy K 𝒱) (T : ℕ)
    (hKT : 3 ≤ Real.log ((K : ℝ) * T)) :
    (∫ ω, |U (empPolicy S M π T ω) - U (pseudoEmp S M π T ω) -
        dU (pseudoEmp S M π T ω) (empPolicy S M π T ω - pseudoEmp S M π T ω)| ∂M.P) ≤
        1 / 2 * β * ∫ ω, N (empPolicy S M π T ω - pseudoEmp S M π T ω) ^ 2 ∂M.P ∧
      1 / 2 * β * (∫ ω, N (empPolicy S M π T ω - pseudoEmp S M π T ω) ^ 2 ∂M.P) ≤
        3 * β * (K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / (2 * υ * T) := by sorry

end EDPMBandit
