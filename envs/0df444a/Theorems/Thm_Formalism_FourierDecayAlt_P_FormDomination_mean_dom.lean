-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_mean_dom
-- name    : Formalism.FourierDecayAlt.P.FormDomination.mean_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:57.994622+00:00
-- url     : https://prove2.me/theorems/9621b12a-32a6-4876-998c-e006501ed3b0
-- title:
--   Form Domination: mean dom
-- statement:
--   The Form Domination construction uses the mean dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L67-L77

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
variable {E W : Type} [Field E] (D : Data E W)

theorem Formalism.FourierDecayAlt.P.FormDomination.mean_dom (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (S : Finset W) (θ : W → ℝ) (hθ : IsProb S θ)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (hc : 0 ≤ c) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) (M : ℝ)
    (hM : ∀ w' ∈ S, D.N0 ε k w' Y κ ≤ M) :
    ∑ t ∈ R, ∑ w' ∈ S, θ w' * D.N0 ε k w' Y (Th t) ≤ c * M := by sorry
