-- Prove2me | Theorems.Thm_Formalism_L2_NCov_W_le
-- name    : Formalism.L2.NCov.W_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:12.291809+00:00
-- url     : https://prove2.me/theorems/7df00059-cb44-4a29-8c18-870919386876
-- title:
--   NCov: W le
-- statement:
--   The NCov construction uses the W le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L97-L99

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

theorem Formalism.L2.NCov.W_le (T : Subalgebra O (End K V)) (χ : T → K) (t : T) :
    W T χ ≤ (t : End K V).maxGenEigenspace (χ t) := by sorry
