-- Prove2me | Theorems.Thm_Formalism_L2_NCov_mem_maxGen_add
-- name    : Formalism.L2.NCov.mem_maxGen_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:51.681122+00:00
-- url     : https://prove2.me/theorems/764bcab8-2899-4df9-a1fb-10de595890e2
-- title:
--   NCov: mem max Gen add
-- statement:
--   The NCov construction uses the mem max Gen add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L33-L43

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

theorem Formalism.L2.NCov.mem_maxGen_add {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A + B).maxGenEigenspace (a + b) := by sorry
