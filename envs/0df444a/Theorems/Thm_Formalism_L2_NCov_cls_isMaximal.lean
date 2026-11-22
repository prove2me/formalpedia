-- Prove2me | Theorems.Thm_Formalism_L2_NCov_cls_isMaximal
-- name    : Formalism.L2.NCov.cls_isMaximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:50.290036+00:00
-- url     : https://prove2.me/theorems/7da3fde4-6502-47a3-8290-5f3cc2aed489
-- title:
--   NCov: cls is Maximal
-- statement:
--   The NCov construction uses the cls is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L121-L124

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
variable [IsLocalRing O]

theorem Formalism.L2.NCov.cls_isMaximal {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : (cls ψ).IsMaximal := by sorry
