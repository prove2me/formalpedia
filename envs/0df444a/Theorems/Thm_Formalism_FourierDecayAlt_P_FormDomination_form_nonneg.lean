-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_form_nonneg
-- name    : Formalism.FourierDecayAlt.P.FormDomination.form_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:46.270659+00:00
-- url     : https://prove2.me/theorems/fb88f782-7aad-4d86-bb41-247b2214042c
-- title:
--   Form Domination: form nonneg
-- statement:
--   The Form Domination construction uses the form nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L10-L22

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder

theorem Formalism.FourierDecayAlt.P.FormDomination.form_nonneg {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by sorry
