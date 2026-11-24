-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_form_core
-- name    : Formalism.L2.Ker.KS.form_core
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:55.060776+00:00
-- url     : https://prove2.me/theorems/e76fc037-4cae-4bb5-bf9c-20dabb0179ad
-- title:
--   KS: form core
-- statement:
--   The KS construction uses the form core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L285-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L285-L320

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

theorem Formalism.L2.Ker.KS.form_core (d : ℕ) (hd : 0 < d) (w1 w2 : ℂ) (hw1 : w1 ≠ 0) (p q r s : ℤ) (hq : 0 < q)
    (h1 : (p : ℂ) * w1 + (q : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w1)
    (h2 : (r : ℂ) * w1 + (s : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w2) :
    4 * q * (-r) = (1 - 2 * p) ^ 2 + d ∧ w1 / q ≠ 0 ∧ w1 = w1 / q * q ∧ w2 = w1 / q * Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d := by sorry
