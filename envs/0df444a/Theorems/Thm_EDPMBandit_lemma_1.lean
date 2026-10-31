-- Prove2me | Theorems.Thm_EDPMBandit_lemma_1
-- name    : EDPMBandit.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:55.190153+00:00
-- url     : https://prove2.me/theorems/b6e664f6-250e-470c-806a-64481d15e810
-- title:
--   Lemma 1 — Lipschitz constant $L=b(1+D^{q-1})$ and pseudo regret decomposition
-- statement:
--   Let $U$ satisfy Requirement 1 of stability with parameters $b>0$, $q\ge1$, and let $i^*$ be an arm with $\Delta_i>0$ for every $i\ne i^*$. Put $L=b(1+D^{q-1})$. Then
--
--   1. $U$ is $L$-Lipschitz on $D^\Delta$: $|U(F_1)-U(F_2)|\le L\|F_1-F_2\|$ for all $F_1,F_2\in D^\Delta$;
--   2. for every admissible policy $\pi$ and every $T\ge1$,
--   $$
--   \bar R_\pi(T)\le\frac{L\rho}T\sum_{i\ne i^*}\Delta_i\,\mathbb E\tau_i(T).
--   $$
--
--   As for linear objectives, the pseudo regret is controlled by the expected number of pulls of the sub-optimal arms.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm. $D^{q-1}$ is `Real.rpow` ($0^0=1$, the paper's value at $D=0$, $q=1$).
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - generalization: U a stable EDPM (both requirements) → Requirement 1 of stability; reason: the proof uses only the modulus of continuity; a stable EDPM satisfies Requirement 1
--   - reading: ρ = max_{i≠i*} ‖F^{(i*)} − F^{(i)}‖/Δ_i, i* ∈ argmax U(F^{(i)}) → hypothesis Δ_i > 0 for every i ≠ i*; reason: ρ is undefined otherwise (division by Δ_i); it also makes i* the unique maximizer
--   - generalization: standing assumption (10): U(F) ≤ U(F^{(i*)}) for all F ∈ D^Δ → not assumed; reason: the statement holds without it (the argument uses only the choice of i* and Δ_i > 0); every instance of the source satisfies the Lean hypotheses
--   - encoding: horizon T, a number of rounds (F̂^π_T and F^π_T divide by T) → T : ℕ with the hypothesis 1 ≤ T; reason: excludes only T = 0, where F̂^π_T and F^π_T are undefined
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.8, Lemma 1

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Lemma 1 (Pseudo regret decomposition), Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.8: "Let U
be a stable EDPM, then U is L-Lipschitz over D^Δ with L = b(1 + D^{q−1}), and we have that
R̄_π(T) ≤ (Lρ/T) ∑_{i≠i*} Δ_i E τ_i(T)."

**Formalization Note.** Requirement 1 of stability (parameters `b > 0`, `q ≥ 1`) is the only
part of stability the statement uses. `Δ_i > 0` for `i ≠ i*` is assumed so that `ρ` (14) is
defined (it also makes `i*` the unique maximizer of `U(F^{(i)})`). `D^{q−1}` is `Real.rpow`
(`0^0 = 1`). The decomposition holds for every admissible policy and every `T ≥ 1`. -/
theorem lemma_1 {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (b q : ℝ)
    (hReq1 : StabilityReq1 S N U M b q) (istar : Fin K)
    (hgap : ∀ i, i ≠ istar → 0 < gap S U M istar i) :
    (∀ F₁ ∈ mixtures S M, ∀ F₂ ∈ mixtures S M,
        |U F₁ - U F₂| ≤ lipConst b q (diam S N M) * N (F₁ - F₂)) ∧
      ∀ (π : Policy K 𝒱) (T : ℕ), 1 ≤ T →
        pseudoRegret S U M istar π T ≤
          lipConst b q (diam S N M) * gapRatio S N U M istar / T *
            ∑ i ∈ Finset.univ.filter (· ≠ istar),
              gap S U M istar i * ∫ ω, (pulls M π i T ω : ℝ) ∂M.P := by sorry

end EDPMBandit
