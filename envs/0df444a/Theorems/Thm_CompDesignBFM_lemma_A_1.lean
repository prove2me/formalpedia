-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_A_1
-- name    : CompDesignBFM.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:22.275783+00:00
-- url     : https://prove2.me/theorems/9bd26543-1156-40a4-8012-e8ecf568e136
-- title:
--   Lemma A.1 — structure of the monotone closure
-- statement:
--   Let $v$ be normalized and nonnegative.
--
--   1. If $v$ is subadditive, then $\hat v$ is normalized, monotone and subadditive.
--   2. If $v$ is XOS, then $\hat v$ is normalized, monotone and XOS.
--
--   This reduces the nonmonotone classes of the goal to monotone ones.
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma A.1, p.40 (PDF 42)

import Mathlib
import Definitions.Def_CompDesignBFM_closure
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace CompDesignBFM

/-- Lemma A.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.40, PDF 42. If `v` is normalized, nonnegative and subadditive, then `v̂` is normalized,
monotone and subadditive. If `v` is normalized, nonnegative and XOS, then `v̂` is normalized, monotone and XOS. -/
theorem lemma_A_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hv : ∀ S, 0 ≤ v S) :
    (BudgetClock.Subadditive.IsSubadditive v →
      closure v ∅ = 0 ∧ IsMonotoneSF (closure v) ∧
        BudgetClock.Subadditive.IsSubadditive (closure v)) ∧
    (IsXOS v → closure v ∅ = 0 ∧ IsMonotoneSF (closure v) ∧ IsXOS (closure v)) := by sorry

end CompDesignBFM
