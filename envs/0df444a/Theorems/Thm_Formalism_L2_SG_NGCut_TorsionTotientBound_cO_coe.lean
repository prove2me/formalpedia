-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_cO_coe
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.cO_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:10.804585+00:00
-- url     : https://prove2.me/theorems/c6d267f6-a9fb-4f0d-ba7c-db7d663cc24e
-- title:
--   Torsion Totient Bound: c O coe
-- statement:
--   The Torsion Totient Bound construction uses the c O coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MemTorsionOfMulConj.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MemTorsionOfMulConj.lean#L15-L15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.cO_coe (y : 𝓞 E) : ((cO E y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := by sorry
