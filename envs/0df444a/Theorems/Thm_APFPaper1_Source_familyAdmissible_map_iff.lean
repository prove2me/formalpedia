-- Prove2me | Theorems.Thm_APFPaper1_Source_familyAdmissible_map_iff
-- name    : APFPaper1.Source.familyAdmissible_map_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:47:21.77437+00:00
-- url     : https://prove2.me/theorems/d33b6ed7-dfa1-4750-9029-4d7f2e6c284e
-- title:
--   Injective relabeling with identical protocols, bills and capacity preserves ledger admissibility
-- statement:
--   Injective relabeling with identical protocols, bills and capacity preserves ledger admissibility.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

theorem APFPaper1.Source.familyAdmissible_map_iff {D D' P R Record : Type*} (f : D' ↪ D)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (T : Finset D') :
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (T.map f) ↔
      familyAdmissible wholeResource calibration maintained (fun p s t => sufficient p s (f t))
        (fun p t s => usesToRealize p (f t) s) C T := by sorry
