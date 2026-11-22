-- Prove2me | Theorems.Thm_Formalism_L2_NCov_algebraMap_end_eq
-- name    : Formalism.L2.NCov.algebraMap_end_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:55.576718+00:00
-- url     : https://prove2.me/theorems/2c2da130-e087-445e-a73c-8eee6c274eae
-- title:
--   NCov: algebra Map end eq
-- statement:
--   The NCov construction uses the algebra Map end eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L101-L104

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem Formalism.L2.NCov.algebraMap_end_eq (c : O) :
    algebraMap O (End K V) c = (algebraMap O K c) • (1 : End K V) := by sorry
