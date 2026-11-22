-- Prove2me | Theorems.Thm_Formalism_L2_NCov_maxGen_smul_one
-- name    : Formalism.L2.NCov.maxGen_smul_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:05.075176+00:00
-- url     : https://prove2.me/theorems/c8830de3-1fd9-43f1-a5ef-a934bd3459be
-- title:
--   NCov: max Gen smul one
-- statement:
--   The NCov construction uses the max Gen smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L50-L54

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
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.NCov.maxGen_smul_one (c : K) : (c • (1 : End K V)).maxGenEigenspace c = ⊤ := by sorry
