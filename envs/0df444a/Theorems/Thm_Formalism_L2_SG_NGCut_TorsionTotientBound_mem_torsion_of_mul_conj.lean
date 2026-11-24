-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_mem_torsion_of_mul_conj
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.mem_torsion_of_mul_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:18.059289+00:00
-- url     : https://prove2.me/theorems/a855b752-dfa9-42ba-b98d-0b63e535b032
-- title:
--   Torsion Totient Bound: mem torsion of mul conj
-- statement:
--   The Torsion Totient Bound construction uses the mem torsion of mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MemTorsionOfMulConj.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MemTorsionOfMulConj.lean#L17-L28

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

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.mem_torsion_of_mul_conj (u : (𝓞 E)ˣ)
    (hu : ((u : 𝓞 E) : E) * IsCMField.complexConj E ((u : 𝓞 E) : E) = 1) : u ∈ Units.torsion E := by sorry
