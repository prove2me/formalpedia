-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_hasDerivAt_md_along_line
-- name    : Formalism.IndefR.Eqv.hasDerivAt_md_along_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:10.188776+00:00
-- url     : https://prove2.me/theorems/da6a3693-1028-471e-958e-eb0d141a2615
-- title:
--   Eqv: has Deriv At md along line
-- statement:
--   The Eqv construction uses the has Deriv At md along line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L16-L29

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

theorem Formalism.IndefR.Eqv.hasDerivAt_md_along_line {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) : ∀ (n : ℕ) (v : Fin n → V) (h : ℝ) (a w : V),
    HasDerivAt (fun s : ℝ => md φ n v h (a + s • w)) (md (fun y => fderiv ℝ φ y w) n v h a) 0
  := by sorry
