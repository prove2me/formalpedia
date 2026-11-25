-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_image_eq_int
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.image_eq_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:11.305472+00:00
-- url     : https://prove2.me/theorems/9231eaee-e5ad-40dd-9541-c78e448f9926
-- title:
--   Alt Inv: image eq int
-- statement:
--   The Alt Inv construction uses the image eq int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L339-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L339-L356

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}

theorem Formalism.L2.FormalSeriesBounds.AltInv.image_eq_int [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t γ} = {F | IntS v F} := by sorry
