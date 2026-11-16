-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_6_2
-- name    : CompDesign.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:58:52.497313+00:00
-- url     : https://prove2.me/theorems/e7d01667-072a-44d3-bd4b-2c1bbec7e9d1
-- title:
--   Theorem 6.2 — rules with (A1)–(A2): $(m+1)$-agent non-monotone submodular instances with a strict equilibrium $L$, $\mathrm{OPT}/v(L)=m$
-- statement:
--   Fix $\lambda\in(0,1)$, a budget $B>0$ and an integer $m\ge\max\{2,\lceil1/\lambda\rceil\}$. Let $p$ be a deterministic cost-oblivious payment rule on $n=m+1$ agents (a map from value functions to payments) that, for every value function $v:2^N\to\mathbb R_{\ge0}$, is nonnegative and budget feasible ($\sum_ip_i(S)\le B$) and satisfies (A1) equal treatment of equal marginal contributions and (A2) positive compensation on uniformly productive coalitions.
--
--   **Theorem 6.2 (Lower bound under equal-marginal treatment).** There are a normalized, nonnegative, submodular and non-monotone value function $v$ and costs with $0<c_i\le\lambda B$ for every $i$ and $\max_ic_i/B=\lambda$, such that the induced game has a strict pure Nash equilibrium $L$ with $v(L)>0$ and
--   $$\frac{\mathrm{OPT}}{v(L)}\ =\ m\ =\ n-1.$$
--
--   Beyond monotone values, natural anonymous cost-oblivious rules suffer a linear price of anarchy even under a large-market condition.
--
--   Differences from the source:
--   - generalization: a rule of (N, v, B) satisfying the conditions at every budget, for every number of agents → a rule P v on Fin (m+1) at one fixed budget B > 0, with the conditions at that B; reason: weaker hypotheses: the source's rule restricted to n = m + 1 agents and the budget B satisfies them
--   - encoding: λ ∈ (0,1); m ≥ max{2, ⌈1/λ⌉} → l with 0 < l < 1; 2 ≤ m and ⌈1/l⌉₊ ≤ m; reason: the same conditions
--   - encoding: max_i c_i/B = λ with 0 < c_i ≤ λB → 0 < c_i ≤ l·B for every i and c_i = l·B for some i; reason: equivalent for B > 0
--   - encoding: OPT/v(L) = m → 0 < v(L) ∧ OPT = m·v(L); reason: equivalent, and the positivity makes the ratio genuine
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 6.2, §6.2.1, p.50 (PDF 53); (A1)–(A2), p.49 (PDF 52)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_EqualMarginalTreatment

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 6.2 (Lower bound under equal-marginal treatment), §6.2.1, p.50 (PDF 53) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Fix
any `λ ∈ (0,1)`, and let `p` be any deterministic cost-oblivious, nonnegative, and budget-feasible
payment rule satisfying (A1)–(A2). For every integer `m ≥ max{2, ⌈1/λ⌉}`, there is an instance with
`n = m + 1` agents, a normalized nonnegative non-monotone submodular value function, and strictly
positive costs satisfying `0 < c_i ≤ λB` for every `i`, where `max_i c_i/B = λ`, such that the induced
game has a strict pure Nash equilibrium `L` and `OPT/v(L) = m = n − 1`.

**Formalization Note.** `λ` is `l`. The budget `B > 0` is fixed and the rule `P` maps value
functions on `Fin (m+1)` to payments, never seeing `c` (cost obliviousness). Nonnegativity, budget
feasibility `∑_i p_i(S) ≤ B`, (A1) and (A2) are assumed for every value function `v : 2^N → ℝ≥0`,
as on p.49 (the proof applies them to a non-monotone `v`). The rule is needed only on `m + 1`
agents. `max_i c_i/B = λ` is: every `c_i ≤ λB` and some `c_i = λB`. `OPT/v(L) = m` is
`0 < v(L) ∧ OPT = m v(L)`. -/
theorem theorem_6_2 (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) (B : ℝ) (hB : 0 < B) (m : ℕ)
    (hm2 : 2 ≤ m) (hml : ⌈1 / l⌉₊ ≤ m)
    (P : (Finset (Fin (m + 1)) → ℝ) → Finset (Fin (m + 1)) → Fin (m + 1) → ℝ)
    (hnn : ∀ v : Finset (Fin (m + 1)) → ℝ, (∀ S, 0 ≤ v S) → ∀ S i, 0 ≤ P v S i)
    (hbf : ∀ v : Finset (Fin (m + 1)) → ℝ, (∀ S, 0 ≤ v S) → ∀ S, ∑ i, P v S i ≤ B)
    (hA1 : EqualMarginalTreatment P) (hA2 : PositiveOnUniform P) :
    ∃ (v : Finset (Fin (m + 1)) → ℝ) (c : Fin (m + 1) → ℝ) (L : Finset (Fin (m + 1))),
      v ∅ = 0 ∧ (∀ S, 0 ≤ v S) ∧ IsSubmodularSF v ∧ ¬ IsMonotoneSF v ∧
      (∀ i, 0 < c i ∧ c i ≤ l * B) ∧ (∃ i, c i = l * B) ∧ IsStrictPNEOf (P v) c L ∧
      0 < v L ∧ CompDesignBFM.OPT v B c = (m : ℝ) * v L := by sorry

end CompDesign.Supplement
