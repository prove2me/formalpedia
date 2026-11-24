-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk4_split
-- name    : Formalism.L2.Th1.F.Hk4.split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:01.881655+00:00
-- url     : https://prove2.me/theorems/a5a7a0c4-f147-438d-bb63-f135a179f6de
-- title:
--   Hk4: split
-- statement:
--   The Hk4 construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L24-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L24-L59

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
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
open scoped BigOperators ComplexConjugate
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk4

theorem Formalism.L2.Th1.F.Hk4.split (h2 : HkRowIntegral) {τ : ℂ} (hτ : τ.im ≠ 0) {b : ℤ × ℤ → ℝ} (hb : Summable b)
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hI : Summable (fun n : ℤ => if n = 0 then 0 else hkInt τ s n)) :
    ∑' n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = ∑' m : ℤ, hk s (m : ℂ) + ∑' p : ℤ × ℤ, cellOff τ s p
        + ∑' n : ℤ, (if n = 0 then 0 else hkInt τ s n) := by sorry
