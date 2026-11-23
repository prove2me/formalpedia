-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_prob_le
-- name    : Formalism.FourierDecayAlt.P.FormDomination.prob_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:10.217903+00:00
-- url     : https://prove2.me/theorems/9522dad3-d64d-4ed7-8300-4c8f5a4f8edd
-- title:
--   Form Domination: prob le
-- statement:
--   The Form Domination construction uses the prob le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L42-L46

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

theorem Formalism.FourierDecayAlt.P.FormDomination.prob_le {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ) (M : ℝ)
    (hg : ∀ a ∈ S, g a ≤ M) : ∑ a ∈ S, θ a * g a ≤ M := by sorry
