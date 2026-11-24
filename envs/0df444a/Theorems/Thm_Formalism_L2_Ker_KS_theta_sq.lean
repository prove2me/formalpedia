-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_theta_sq
-- name    : Formalism.L2.Ker.KS.theta_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:40.058329+00:00
-- url     : https://prove2.me/theorems/c8e07db6-3a0b-4817-8be0-2d6bb9a12faa
-- title:
--   KS: theta sq
-- statement:
--   The KS construction uses the theta sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L57-L64

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_theta_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem Formalism.L2.Ker.KS.theta_sq (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta b d = (b : ℂ) * Formalism.L2.Th1.F.cmTheta b d - (a : ℂ) * (c : ℂ) := by sorry
