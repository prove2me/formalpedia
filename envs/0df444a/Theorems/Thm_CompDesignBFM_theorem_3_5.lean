-- Prove2me | Theorems.Thm_CompDesignBFM_theorem_3_5
-- name    : CompDesignBFM.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:13.620201+00:00
-- url     : https://prove2.me/theorems/82bfcbf6-a08f-4bd8-baa1-19e58fc62c98
-- title:
--   Theorem 3.5 — a self-bounding proxy within a factor 2 of any subadditive function
-- statement:
--   Let $v$ be normalized, monotone and subadditive. Then the smoothed value $\tilde v$ is normalized, monotone, subadditive and self-bounding, and for every $S\subseteq N$,
--
--   $$\frac12v(S)\le\tilde v(S)\le v(S).\tag{8}$$
--
--   It allows the marginal-contribution branch to run on subadditive values with a loss of only a factor 2.
--
--   Differences from the source:
--   - generalization: there exists a function ṽ with these properties → the explicit witness ṽ = smoothed v (the proof's witness, p.19); reason: naming the witness implies the printed existence statement
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.5, p.18 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_CompDesignBFM_smoothed
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace CompDesignBFM

/-- Theorem 3.5, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.18, PDF 20 (proof p.19, PDF 21). For normalized, monotone, subadditive `v`, the
smoothed value `ṽ` is normalized, monotone, subadditive and self-bounding, and `v(S)/2 ≤ ṽ(S) ≤ v(S)` for every
`S` (eq. (8)).
**Formalization Note.** The paper states "there exists a function"; this names the witness of its proof. -/
theorem theorem_3_5 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hm : IsMonotoneSF v)
    (hs : BudgetClock.Subadditive.IsSubadditive v) :
    smoothed v ∅ = 0 ∧ IsMonotoneSF (smoothed v) ∧
      BudgetClock.Subadditive.IsSubadditive (smoothed v) ∧ IsSelfBounding (smoothed v) ∧
      ∀ S, 1 / 2 * v S ≤ smoothed v S ∧ smoothed v S ≤ v S := by sorry

end CompDesignBFM
