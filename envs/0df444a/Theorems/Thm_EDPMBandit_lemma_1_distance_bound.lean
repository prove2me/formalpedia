-- Prove2me | Theorems.Thm_EDPMBandit_lemma_1_distance_bound
-- name    : EDPMBandit.lemma_1_distance_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:30.727478+00:00
-- url     : https://prove2.me/theorems/5cced247-0ee5-436a-9ecc-901f4d17d538
-- title:
--   Proof of Lemma 1, display — $\mathbb E\|F^{(i^*)}-F^\pi_T\|\le\frac\rho T\sum_{i\ne i^*}\Delta_i\mathbb E\tau_i(T)$
-- statement:
--   Let $i^*$ be an arm with $\Delta_i>0$ for every $i\ne i^*$. For every admissible policy $\pi$ and every $T\ge1$,
--
--   $$
--   \mathbb E\|F^{(i^*)}-F^\pi_T\|\le\frac\rho T\sum_{i\ne i^*}\Delta_i\,\mathbb E\tau_i(T).
--   $$
--
--   This is the chain of the proof of Lemma 1 without the Lipschitz factor $L$; it is the form used in the proof of Theorem 4, where the bound of Theorem 2 controls $\mathbb E\|F^{U\text{-}UCB}_T-F^{(i^*)}\|$.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - generalization: Lemma 1: U a stable EDPM → no stability hypothesis; reason: the distance chain does not involve U except through Δ_i and ρ; every stable EDPM is covered
--   - reading: ρ = max_{i≠i*} ‖F^{(i*)} − F^{(i)}‖/Δ_i, i* ∈ argmax U(F^{(i)}) → hypothesis Δ_i > 0 for every i ≠ i*; reason: ρ is undefined otherwise (division by Δ_i); it also makes i* the unique maximizer
--   - generalization: standing assumption (10): U(F) ≤ U(F^{(i*)}) for all F ∈ D^Δ → not assumed; reason: the statement holds without it (the argument uses only the choice of i* and Δ_i > 0); every instance of the source satisfies the Lean hypotheses
--   - encoding: horizon T, a number of rounds (F̂^π_T and F^π_T divide by T) → T : ℕ with the hypothesis 1 ≤ T; reason: excludes only T = 0, where F̂^π_T and F^π_T are undefined
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.23, proof of Lemma 1, the display (the chain after its first inequality, divided by L)

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Proof of Lemma 1, the display, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.23, divided by
`L`: `E‖F^{(i*)} − F^π_T‖ ≤ (ρ/T) ∑_{i≠i*} Δ_i E τ_i(T)`. This is the form used in the proof of
Theorem 4 ("Theorem 2 actually bounds L E‖F^{U−UCB}_T − F^{(i*)}‖", p.11).

**Formalization Note.** Only `Δ_i > 0` for `i ≠ i*` (so that `ρ` is defined) is assumed; no
stability. Every admissible policy, every `T ≥ 1`. -/
theorem lemma_1_distance_bound {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*}
    [MeasurableSpace 𝒱] (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ)
    (M : BanditModel K Ω 𝒱) (istar : Fin K) (hgap : ∀ i, i ≠ istar → 0 < gap S U M istar i)
    (π : Policy K 𝒱) (T : ℕ) (hT : 1 ≤ T) :
    ∫ ω, N (armDist S M istar - pseudoEmp S M π T ω) ∂M.P ≤
      gapRatio S N U M istar / T *
        ∑ i ∈ Finset.univ.filter (· ≠ istar),
          gap S U M istar i * ∫ ω, (pulls M π i T ω : ℝ) ∂M.P := by sorry

end EDPMBandit
