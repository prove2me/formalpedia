-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupSubstitution_subst_X_add_X
-- name    : Formalism.FG.FormalGroupSubstitution.subst_X_add_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:10.649752+00:00
-- url     : https://prove2.me/theorems/6279aa02-741d-496a-9de2-77e11a4db8a1
-- title:
--   Formal Group Substitution: subst X add X
-- statement:
--   The Formal Group Substitution construction uses the subst X add X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L9-L13

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries

theorem Formalism.FG.FormalGroupSubstitution.subst_X_add_X {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p q : σ) :
    subst a (X p + X q : MvPowerSeries σ R) = a p + a q := by sorry
