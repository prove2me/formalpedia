-- Prove2me | Theorems.Thm_EDPMBandit_expected_differential_eq_zero
-- name    : EDPMBandit.expected_differential_eq_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:28.123664+00:00
-- url     : https://prove2.me/theorems/b3adb88c-df3f-47c6-a272-69756b3e4031
-- title:
--   Proof of Theorem 3, second display — $\mathbb E[\partial U(F)\cdot(\hat F^\pi_T-F^\pi_T)]=0$
-- statement:
--   Assume Requirement 2 of stability (parameter $\upsilon$) and the standing measurability assumption. Let $F\in D^\Delta$ and let $\partial U(F)$ be the differential of $U$ at $F$ in the sense of Definition 2 with $M_0=\infty$ and parameter $\beta\ge0$, i.e. a bounded linear functional on $L$ with $|U(G)-U(F)-\partial U(F)\cdot(G-F)|\le\frac12\beta\|G-F\|^2$ for all $G\in L$. Then for every admissible policy $\pi$ and every $T\ge1$,
--
--   $$
--   \mathbb E\big[\partial U(F)\cdot(\hat F^\pi_T-F^\pi_T)\big]=0.
--   $$
--
--   This removes the first-order term in the expansion of the horizon gap $\mathbb E[U(\hat F^\pi_T)-U(F^\pi_T)]$.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - generalization: inside Theorem 3: U stable and smooth with M₀ = ∞ → Requirement 2 of stability and the differential at the given F only; reason: the claim concerns ∂U(F) at one F and the concentration of the empirical distributions only; a stable, smooth EDPM satisfies these hypotheses
--   - reading: standing assumption (p.5): the expectations exist and are finite → MeasurableAlongEmp: x ↦ U(G + c·F̂_t(x)) and x ↦ ‖G + c·F̂_t(x)‖ are Borel measurable for all t, G, c; reason: makes every expectation the paper writes the integral of a measurable function; finiteness follows from stability
--   - encoding: ∂U(F), the differential of U at F → any bounded linear functional dU with the smoothness bound at F (IsDifferentialAt); reason: the quadratic bound determines the functional uniquely, and it is the differential
--   - encoding: horizon T, a number of rounds (F̂^π_T and F^π_T divide by T) → T : ℕ with the hypothesis 1 ≤ T; reason: excludes only T = 0, where F̂^π_T and F^π_T are undefined
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.25, proof of Theorem 3, second display

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Proof of Theorem 3, second display, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.25: "Since
∂U is a linear operator, we conclude that E[∂U(F)·(F̂^π_T − F^π_T)] = 0, ∀F ∈ D^Δ."

**Formalization Note.** `∂U(F)` is any bounded linear functional `dU` satisfying the smoothness
bound of Definition 2 (`M₀ = ∞`) at `F` (`IsDifferentialAt`); that bound determines it uniquely.
The hypotheses are Requirement 2 of stability, `β ≥ 0`, the differential at `F`, and the
standing measurability assumption of p.5 (`MeasurableAlongEmp`). Every admissible policy,
every `T ≥ 1`. -/
theorem expected_differential_eq_zero {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*}
    [MeasurableSpace 𝒱] (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ)
    (M : BanditModel K Ω 𝒱) (υ β : ℝ) (hReq2 : StabilityReq2 S N M υ) (hβ : 0 ≤ β)
    (hmeas : MeasurableAlongEmp S N U) (F : S.L) (hF : F ∈ mixtures S M) (dU : S.L →ₗ[ℝ] ℝ)
    (hdU : IsDifferentialAt S N U β F dU) (π : Policy K 𝒱) (T : ℕ) (hT : 1 ≤ T) :
    ∫ ω, dU (empPolicy S M π T ω - pseudoEmp S M π T ω) ∂M.P = 0 := by sorry

end EDPMBandit
