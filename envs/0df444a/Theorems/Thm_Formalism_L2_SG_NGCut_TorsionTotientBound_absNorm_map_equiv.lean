-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_absNorm_map_equiv
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.absNorm_map_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:18.608899+00:00
-- url     : https://prove2.me/theorems/0c864eff-0951-4725-8b7f-64fcdab0f8fb
-- title:
--   Torsion Totient Bound: abs Norm map equiv
-- statement:
--   The Torsion Totient Bound construction uses the abs Norm map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L49-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.absNorm_map_equiv (σ : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map σ) = Ideal.absNorm I := by sorry
