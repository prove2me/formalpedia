-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcCut_normalizing_constant_eq
-- name    : Formalism.L2.SG.Pf.NcCut.normalizing_constant_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:30.032806+00:00
-- url     : https://prove2.me/theorems/2f8ba6dc-0579-406b-96ff-cc6d9451eb83
-- title:
--   Nc Cut: normalizing constant eq
-- statement:
--   The Nc Cut construction uses the normalizing constant eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormalizingConstantEq.lean#L33-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormalizingConstantEq.lean#L33-L61

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NormalizingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcCut
open Formalism.FourierDecayAlt.S3
variable {P : Type} [Fintype P] (B : MassData P)

theorem Formalism.L2.SG.Pf.NcCut.normalizing_constant_eq (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) :
    B.n0c = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' := by sorry
