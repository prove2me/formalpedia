-- Prove2me | Theorems.Thm_EDPMBandit_theorem_2
-- name    : EDPMBandit.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:10.73498+00:00
-- url     : https://prove2.me/theorems/0d0e98ac-fd1b-4e23-a073-79a9d3726e8d
-- title:
--   Theorem 2 — pseudo regret of U-UCB
-- statement:
--   Let $U$ be stable with parameters $\upsilon,b,q$, let $i^*$ be an arm with $\Delta_i>0$ for every $i\ne i^*$, let $\gamma>2$, and assume the standing measurability assumption. With $L=b(1+D^{q-1})$ as in Lemma 1, every run of U-UCB satisfies, for every $T\ge1$,
--
--   $$
--   \bar R_{U\text{-}UCB}(T)\le\frac{L\rho}T\sum_{i\ne i^*}\Big(\frac{\gamma\Delta_i\log T}{\varphi(\Delta_i/2)}+\frac{\gamma+6}{\gamma-2}\Delta_i\Big).
--   $$
--
--   The pseudo regret of U-UCB is $O(\log T/T)$, as for the classical UCB policy.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - reading: ρ = max_{i≠i*} ‖F^{(i*)} − F^{(i)}‖/Δ_i, i* ∈ argmax U(F^{(i)}) → hypothesis Δ_i > 0 for every i ≠ i*; reason: ρ is undefined otherwise (division by Δ_i); it also makes i* the unique maximizer
--   - reading: U-UCB (15): π_t ∈ argmax of the index for t ≥ K+1, each arm sampled once for t ≤ K, no tie-breaking rule → IsUUCBRun: an admissible policy with τ_i(K) = 1 for all i and the argmax property at every round t ≥ K+1 and every outcome; reason: U-UCB must be an admissible (non-anticipating) policy for the analysis; every non-anticipating tie-breaking and initial order is allowed
--   - reading: standing assumption (p.5): the expectations exist and are finite → MeasurableAlongEmp: x ↦ U(G + c·F̂_t(x)) and x ↦ ‖G + c·F̂_t(x)‖ are Borel measurable for all t, G, c; reason: makes every expectation the paper writes the integral of a measurable function; finiteness follows from stability
--   - generalization: standing assumption (10): U(F) ≤ U(F^{(i*)}) for all F ∈ D^Δ → not assumed; reason: the statement holds without it (the argument uses only the choice of i* and Δ_i > 0); every instance of the source satisfies the Lean hypotheses
--   - encoding: horizon T, a number of rounds (F̂^π_T and F^π_T divide by T) → T : ℕ with the hypothesis 1 ≤ T; reason: excludes only T = 0, where F̂^π_T and F^π_T are undefined
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.8, Theorem 2

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions
import Definitions.Def_EDPMBandit_UUCB

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Theorem 2 (U − UCB Pseudo Regret), Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.8: "Let U be a
stable EDPM. If Δ_i > 0 for all i ≠ i*, then for L defined in Lemma 1 and γ > 2 we have that
R̄_{U−UCB}(T) ≤ (Lρ/T) ∑_{i≠i*} (γΔ_i log T/φ(Δ_i/2) + ((γ + 6)/(γ − 2)) Δ_i)."

**Formalization Note.** `L = b(1 + D^{q−1})` (`lipConst`), `ρ` and `D` as in (14). `π` is any
U-UCB run (`IsUUCBRun`) with any non-anticipating tie-breaking; the standing measurability
assumption of p.5 is assumed. Every horizon `T ≥ 1`; natural logarithm. -/
theorem theorem_2 {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (υ b q γ : ℝ)
    (hstab : IsStable S N U M υ b q) (istar : Fin K)
    (hgap : ∀ i, i ≠ istar → 0 < gap S U M istar i) (hγ : 2 < γ)
    (hmeas : MeasurableAlongEmp S N U) (π : Policy K 𝒱) (hπ : IsUUCBRun S U M υ b q γ π)
    (T : ℕ) (hT : 1 ≤ T) :
    pseudoRegret S U M istar π T ≤
      lipConst b q (diam S N M) * gapRatio S N U M istar / T *
        ∑ i ∈ Finset.univ.filter (· ≠ istar),
          (γ * gap S U M istar i * Real.log T / phi υ b q (gap S U M istar i / 2) +
            (γ + 6) / (γ - 2) * gap S U M istar i) := by sorry

end EDPMBandit
