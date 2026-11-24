-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Ker_card_quot
-- name    : Formalism.L2.Th1.F.Ker.card_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:12.907785+00:00
-- url     : https://prove2.me/theorems/2474e7d1-d419-4961-8cb3-5e64f0b4f5f1
-- title:
--   Ker: card quot
-- statement:
--   The Ker construction uses the card quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L104-L113

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
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
open Formalism.L2.Th1.F.Ker

theorem Formalism.L2.Th1.F.Ker.card_quot (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    ((Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) : ℕ) : ℝ) = Complex.normSq α := by sorry
