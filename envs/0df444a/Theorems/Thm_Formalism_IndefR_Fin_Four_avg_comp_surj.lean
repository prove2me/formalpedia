-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_avg_comp_surj
-- name    : Formalism.IndefR.Fin.Four.avg_comp_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:11.690646+00:00
-- url     : https://prove2.me/theorems/82e20722-7253-41fe-a9fd-3ac033abb869
-- title:
--   Four: avg comp surj
-- statement:
--   The Four construction uses the avg comp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L62-L65

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]

theorem Formalism.IndefR.Fin.Four.avg_comp_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by sorry
