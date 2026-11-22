-- Prove2me | Theorems.Thm_Formalism_L2_NCov_pt_injective
-- name    : Formalism.L2.NCov.pt_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:49.750721+00:00
-- url     : https://prove2.me/theorems/ec8e62b6-647c-41c6-ad87-79d622fd88b5
-- title:
--   NCov: pt injective
-- statement:
--   The NCov construction uses the pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L106-L108

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

theorem Formalism.L2.NCov.pt_injective {T : Subalgebra O (End K V)} (hinj : Function.Injective (algebraMap O K)) :
    Function.Injective (pt : (T →ₐ[O] O) → T → K) := by sorry
