-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_fixed_by_products_is_automatic
-- name    : APFPaper1.RecordOccupant.fixed_by_products_is_automatic
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:35:13.889758+00:00
-- url     : https://prove2.me/theorems/4ac7efaa-d53e-46e4-80a7-b32d0edc70ad
-- title:
--   fixed by products is automatic
-- statement:
--   Result: fixed by products is automatic. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem fixed_by_products_is_automatic {β : Type*} [Zero β] (reads : D → X → Bool) (A : Set D)
--       [DecidablePred (· ∈ A)] (R : X → β)
--       (h0 : ∀ z x y : X, IsProductAcross reads A z x y → R z = 0) (z : X) : R z = 0
--   ```
--
--   Module context and limits: IsProductAcross is equality of readings on the two sides of a cut. Every state is its own such product; EveryCombinationHeld gives finite recombination. This is not quantum state factorization or physical local tomography.
--
--   Source scope parameters:
--
--   ```lean
--   variable {X D : Type*}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper1_RecordOccupant_products_across_a_cut:58; pullbacks v39; source SHA-256 5076686a0b996cdce81f0bc04d7e6a785ccd4e30e78d18dcb8dadf0c87c14beb']

import Definitions.Def_APFPaper1_RecordOccupant_products_across_a_cut_Vocabulary
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false

namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1
open APFPaper1.RecordOccupant
variable {X D : Type*}

theorem APFPaper1.RecordOccupant.fixed_by_products_is_automatic {β : Type*} [Zero β] (reads : D → X → Bool) (A : Set D)
    [DecidablePred (· ∈ A)] (R : X → β)
    (h0 : ∀ z x y : X, IsProductAcross reads A z x y → R z = 0) (z : X) : R z = 0 := by sorry
