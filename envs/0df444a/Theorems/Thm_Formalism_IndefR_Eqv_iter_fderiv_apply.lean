-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_iter_fderiv_apply
-- name    : Formalism.IndefR.Eqv.iter_fderiv_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:04.161197+00:00
-- url     : https://prove2.me/theorems/018fa4cd-3ec3-4dc0-ace6-9fb99864011c
-- title:
--   Eqv: iter fderiv apply
-- statement:
--   The Eqv construction uses the iter fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L45-L54

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem Formalism.IndefR.Eqv.iter_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w : V) (a : V) (vs : Fin n → V) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y w) a vs = iteratedFDeriv ℝ (n + 1) φ a (Fin.cons w vs) := by sorry
