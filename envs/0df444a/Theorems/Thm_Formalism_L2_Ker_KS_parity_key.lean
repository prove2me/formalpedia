-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_parity_key
-- name    : Formalism.L2.Ker.KS.parity_key
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:17.502785+00:00
-- url     : https://prove2.me/theorems/d5a76604-bf41-49d9-bba0-ff7c7c6e6c65
-- title:
--   KS: parity key
-- statement:
--   The KS construction uses the parity key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L143-L147

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
omit a b c d lam

theorem Formalism.L2.Ker.KS.parity_key (r s k a c : ℤ) (hc : Even c) (ha : ¬ Even a) (h3 : ¬ (Even (-s * c - k * r) ∧ Even (r * a + s * (k + 1))))
    (h4 : ¬ (Even (r - (-s * c - k * r)) ∧ Even (s - (r * a + s * (k + 1))))) : Even (r - 1) ∧ Even s := by sorry
