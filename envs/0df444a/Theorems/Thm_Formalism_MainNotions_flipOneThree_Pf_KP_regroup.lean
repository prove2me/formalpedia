-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_KP_regroup
-- name    : Formalism.MainNotions.flipOneThree.Pf.KP.regroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:03.152565+00:00
-- url     : https://prove2.me/theorems/368e53cb-4d32-44a1-a389-975515ad0bbd
-- title:
--   KP: regroup
-- statement:
--   The KP construction uses the regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/TensorKP.lean#L81-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/TensorKP.lean#L81-L116

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_TensorKP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open MvPolynomial
open MvPolynomial
open MvPolynomial
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP

theorem Formalism.MainNotions.flipOneThree.Pf.KP.regroup {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {T α : Type} [Fintype T]
    [DecidableEq T] (N : T × Bool → Submodule R (MvPolynomial α K))
    (y : T → MvPolynomial (Bool × α) K)
    (hy : ∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)}) :
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K,
        (∀ x, F x ∈ N x) ∧ P = ∏ x, rename (fun v => (x, v)) (F x)} := by sorry
