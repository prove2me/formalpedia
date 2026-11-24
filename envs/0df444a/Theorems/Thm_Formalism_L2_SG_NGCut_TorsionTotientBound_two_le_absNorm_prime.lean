-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_two_le_absNorm_prime
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.two_le_absNorm_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:26.298166+00:00
-- url     : https://prove2.me/theorems/bb6798be-d13f-43b8-8f42-f3f8d31caa2a
-- title:
--   Torsion Totient Bound: two le abs Norm prime
-- statement:
--   The Torsion Totient Bound construction uses the two le abs Norm prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TwoLeAbsNormPrime.lean#L12-L15

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

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.two_le_absNorm_prime {P : Ideal (𝓞 E)} (hP : P.IsPrime) (h0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by sorry
