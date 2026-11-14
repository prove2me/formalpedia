-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_map
-- name    : APFPaper1.Source.familyCost_map
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:47:21.86+00:00
-- url     : https://prove2.me/theorems/fa178f9b-5ff8-445e-a732-c8bc0bbed97a
-- title:
--   Injective relabeling with identical protocols and bills preserves real family cost exactly
-- statement:
--   Injective relabeling with identical protocols and bills preserves real family cost exactly.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

theorem APFPaper1.Source.familyCost_map {D D' P R Record : Type*} (f : D' ↪ D)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (T : Finset D') :
    familyCost wholeResource calibration maintained sufficient usesToRealize (T.map f) =
      familyCost wholeResource calibration maintained (fun p s t => sufficient p s (f t))
        (fun p t s => usesToRealize p (f t) s) T := by sorry
