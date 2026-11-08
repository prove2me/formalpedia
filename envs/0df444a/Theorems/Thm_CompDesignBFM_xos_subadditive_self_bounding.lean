-- Prove2me | Theorems.Thm_CompDesignBFM_xos_subadditive_self_bounding
-- name    : CompDesignBFM.xos_subadditive_self_bounding
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:15.000532+00:00
-- url     : https://prove2.me/theorems/cf1ab4dd-d898-4b16-b66f-4d13d2d7c3a4
-- title:
--   §3.2.1 — monotone XOS functions are subadditive and self-bounding
-- statement:
--   If $v$ is XOS and monotone, then $v$ is subadditive and self-bounding. Consequently $v$ can serve as its own proxy $F=v$ in the marginal-contribution branch.
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §3.2.1, p.17 (PDF 19)

import Mathlib
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace CompDesignBFM

/-- §3.2.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.17, PDF 19. Monotone XOS functions are both subadditive and self-bounding. -/
theorem xos_subadditive_self_bounding {n : ℕ} (v : Finset (Fin n) → ℝ) (hx : IsXOS v)
    (hm : IsMonotoneSF v) :
    BudgetClock.Subadditive.IsSubadditive v ∧ IsSelfBounding v := by sorry

end CompDesignBFM
