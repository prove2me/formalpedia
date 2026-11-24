-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_theta_pt
-- name    : Formalism.L2.Ker.KS.theta_pt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:57.415921+00:00
-- url     : https://prove2.me/theorems/721716db-e152-4b07-8ef6-7687309867c9
-- title:
--   KS: theta pt
-- statement:
--   The KS construction uses the theta pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L72-L79

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

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

theorem Formalism.L2.Ker.KS.theta_pt (h : 4 * (a : ℤ) * c = b ^ 2 + d) (k : ℤ) (hb : b = 2 * k + 1) (u v : ℝ) :
    Formalism.L2.Th1.F.cmTheta 1 d * pt a b d lam u v = pt a b d lam (-v * c - k * u) (u * a + v * (k + 1)) := by sorry
