-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_half_period_standard_CM
-- name    : Formalism.L2.Ker.KS.half_period_standard_CM
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:54.361261+00:00
-- url     : https://prove2.me/theorems/bcc16723-0688-4db2-bf48-570a6e3130f9
-- title:
--   KS: half period standard CM
-- statement:
--   The KS construction uses the half period standard CM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L115-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L115-L140

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
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

theorem Formalism.L2.Ker.KS.half_period_standard_CM (hcm : CmOK a b c d) :
    2 * (lam * a / 2) ∈ (cmL a b d ha hd lam hlam).lattice ∧
    Formalism.L2.Th1.F.cmTheta 1 d * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice ∧
    (1 - Formalism.L2.Th1.F.cmTheta 1 d) * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice := by sorry
