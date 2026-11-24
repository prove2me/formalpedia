-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_lin
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.W_lin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:10:02.965921+00:00
-- url     : https://prove2.me/theorems/11a29682-3a31-417b-8944-85ad1e0d3af8
-- title:
--   List Sum Splittings: W lin
-- statement:
--   The List Sum Splittings construction uses the W lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L247-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L247-L254

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.W_lin (ℓ : Mat k r →ₗ[ℝ] ℂ) :
    ∀ a : List (Bool × Mat k r), ∃ ℓ' : Mat k r →ₗ[ℝ] ℂ, W a (fun g => ℓ g) = fun g => ℓ' g := by sorry
