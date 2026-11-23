-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_md_succ_sub
-- name    : Formalism.IndefR.Eqv.md_succ_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:08.012868+00:00
-- url     : https://prove2.me/theorems/6098ac85-b9c2-4eff-b35e-41236dd46cb4
-- title:
--   Eqv: md succ sub
-- statement:
--   The Eqv construction uses the md succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L59-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L59-L95

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

theorem Formalism.IndefR.Eqv.md_succ_sub (φ : V → ℂ) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin (n + 1) → V) {h : ℝ} (hh : 0 < h) (b : V)
    (T : ℂ) (ε : ℝ) (hε : ∀ s ∈ Set.Icc (0 : ℝ) h,
      ‖md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0) - T‖ ≤ ε) :
    ‖md φ (n + 1) v h b - T‖ ≤ ε := by sorry
