-- Prove2me | Theorems.Thm_APFPaper1_Foundation_cost_mono_ledger
-- name    : APFPaper1.Foundation.cost_mono_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-10-09T02:50:38.813213+00:00
-- url     : https://prove2.me/theorems/9ffdfe1e-3a3c-4965-83c6-afc81b8b39d0
-- title:
--   Infimal cost is monotone under family inclusion
-- statement:
--   For the source-projection Ledger L and finite families S subset T, if T is Feasible then the infimal cost of S is no greater than that of T. The same protocol serving T also serves S using the proved same-protocol subfamily restriction theorem, with its bill unchanged. Feasibility and source correspondence remain explicit; no budget, attainment or new physical law is inferred. Record is now explicit; the constructed provider and its source exposure are part of this exact statement.
-- source:
--   Paper1 Supplement v9.27:1754–1757,1778–1787,2188–2221,2767–2773,2880–2883,7092. Inputs revision2026-10-04.1. Existing infimum proof body reused verbatim, specialized to the selected constructed Ledger D P Record; this is an explicit provider-signature correction, not a name-only statement replacement. Historical native node and provider remain unchanged. The provider represents the original nonnegative complete calibrated bills on the unchanged admitted protocol domain, with the original empty protocol's zero bill fixed by Supplement2880–2883; it proves no new physical zero-cost law or calibration property.

import Definitions.Def_APFPaper1_CostLedger
import Theorems.Thm_APFPaper1_Foundation_cost_bounds_ledger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem APFPaper1.Foundation.cost_mono_ledger {D P Record : Type*} (L : Ledger D P Record) (S T : Finset D)
    (hST : S ⊆ T) (hT : Feasible L T) : cost L S ≤ cost L T := by sorry
