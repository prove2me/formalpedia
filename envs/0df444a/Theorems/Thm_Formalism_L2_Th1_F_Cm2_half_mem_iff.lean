-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm2_half_mem_iff
-- name    : Formalism.L2.Th1.F.Cm2.half_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:46.553814+00:00
-- url     : https://prove2.me/theorems/7b765db7-1ee6-4e23-bc92-6f63e193dfef
-- title:
--   Cm2: half mem iff
-- statement:
--   The Cm2 construction uses the half mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L13-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Cm2
open Cm1

theorem Formalism.L2.Th1.F.Cm2.half_mem_iff (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n : ℤ) :
    ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2 ∈ (cmPair a b d ha hd).lattice ↔ Even m ∧ Even n := by sorry
