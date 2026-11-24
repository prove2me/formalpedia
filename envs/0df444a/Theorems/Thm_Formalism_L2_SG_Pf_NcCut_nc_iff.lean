-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcCut_nc_iff
-- name    : Formalism.L2.SG.Pf.NcCut.nc_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:27.645719+00:00
-- url     : https://prove2.me/theorems/ed5a311f-a38d-47ab-ae8c-077b9b2db555
-- title:
--   Nc Cut: nc iff
-- statement:
--   The Nc Cut construction uses the nc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormalizingConstantEq.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormalizingConstantEq.lean#L63-L71

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

theorem Formalism.L2.SG.Pf.NcCut.nc_iff (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) (c ng kap : ℝ) (hkap : kap ≠ 0) :
    c = B.n0c * ng / (B.al * kap) ↔
      c * B.al * kap = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) *
        B.μKnat / B.μH' * ng := by sorry
