-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_12
-- name    : BudgetAgg.NashChar.Supplement.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:09:38.238107+00:00
-- url     : https://prove2.me/theorems/32c06cf6-3f81-4c30-a225-41a16a4e613d
-- title:
--   Lemma 12 (used in the proof of Theorem 5) — m = 2, n = 1: continuous and strategyproof iff f(p) = med(p, α₀, α₁)
-- statement:
--   Let $m=2$, $n=1$, and let $U\subseteq U_{SP}$ be a domain of single-peaked utilities on $[0,1]$ containing at least one utility for every peak. A mechanism $f:[0,1]\to[0,1]$ is continuous and strategyproof on $U$ if and only if there are $0\le\alpha_0\le\alpha_1\le1$ with
--
--   $$f(p)=\mathrm{med}(p,\alpha_0,\alpha_1)\qquad\text{for all }p\in[0,1].$$
--
--   It is the one-agent building block of Lemma 13 and hence of Theorems 5 and 6.
--
--   **Formalization Note** A one-agent profile is a map `Fin 1 → unitInterval`; $\mathrm{med}(p,\alpha_0,\alpha_1)$ is the generalized median with peaks $(p)$ and phantoms $(\alpha_0,\alpha_1)$.
--
--   Differences from the source:
--   - encoding: m = 2: outcomes and peaks are scalars in [0, 1], the share of b (§7, p. 17) → Profile2 n = Fin n → unitInterval, Mechanism2 n = Profile2 n → unitInterval (tops-only); reason: the identification of ∆2 with [0, 1] made on p. 17
--   - encoding: arbitrary domain U ⊆ U_SP with at least one utility per peak (§7, p. 17); single-peakedness = star-shapedness (1) for m = 2 → U : Set (ℝ → ℝ) with IsSPDomain U: every u ∈ U satisfies (1) on [0, 1] at some peak p, and every p ∈ [0, 1] is the peak of some u ∈ U; values of u outside [0, 1] are never used; reason: a utility on [0, 1] extends to ℝ in any way; condition (1) is evaluated only on [0, 1]
--   - encoding: strategyproofness (Definition 8, |N′| = 1) on the domain U → IsSP2 U f: for every i, P, misreport p′ and u ∈ U single-peaked at the true peak P i, u(f(P with p_i replaced by p′)) ≤ u(f(P)); reason: an agent with peak p_i may hold any utility of U peaked at p_i, so the inequality must hold for each of them
--   - encoding: med(x_1, …, x_{2k+1}) (p. 18) → med sorts the 2k+1 values ascending and takes index k (0-based), i.e. the (k+1)-th smallest; reason: definition of the median of an odd number of reals
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the product topology on Fin n → unitInterval and the subspace topology on unitInterval; reason: for m = 2 the ℓ1 distance on ∆2 is twice the distance of the b-shares, and all norms on a finite-dimensional space induce the same topology (p. 8)
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 36, Lemma 12 (proof p. 37)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

namespace BudgetAgg.NashChar.Supplement

/-- Lemma 12, p. 36: for `m = 2`, `n = 1` and any admissible domain `U ⊆ U_SP`, a
mechanism is continuous and strategyproof iff it is `p ↦ med(p, α₀, α₁)` for some
`0 ≤ α₀ ≤ α₁ ≤ 1`. -/
theorem lemma_12 (U : Set (ℝ → ℝ)) (hU : IsSPDomain U) (f : Mechanism2 1) :
    (Continuous f ∧ IsSP2 U f) ↔
      ∃ α₀ α₁ : ℝ, 0 ≤ α₀ ∧ α₀ ≤ α₁ ∧ α₁ ≤ 1 ∧
        ∀ P : Profile2 1, (f P : ℝ) = genMedian ![α₀, α₁] P := by sorry

end BudgetAgg.NashChar.Supplement
