-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_sum_baseGram_le
-- name    : Formalism.FourierDecayAlt.P.FormDomination.sum_baseGram_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:59.860838+00:00
-- url     : https://prove2.me/theorems/8a210d4a-45f2-45a0-9ef1-40f48bd5d8cf
-- title:
--   Form Domination: sum base Gram le
-- statement:
--   The Form Domination construction uses the sum base Gram le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean#L58-L65

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

theorem Formalism.FourierDecayAlt.P.FormDomination.sum_baseGram_le (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) :
    ∑ t ∈ R, D.N0 ε k w Y (Th t) ≤ c * D.N0 ε k w Y κ := by sorry
