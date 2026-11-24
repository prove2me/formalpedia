-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_update
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_update
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:05.470097+00:00
-- url     : https://prove2.me/theorems/ec4fa626-95b9-43d1-8323-9973a1c87ec5
-- title:
--   Hermitian Form Factor: gram update
-- statement:
--   The Hermitian Form Factor construction uses the gram update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L582-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L582-L606

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_update (X : Q → Q → ℂ) (j₀ : Q) (n x₀ : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (hx₀ : star n ⬝ᵥ x₀ = 0) (ζ : ℂ) :
    gram (Function.update X j₀ (x₀ + ζ • n)) =
      gram (Function.update X j₀ x₀) + (Complex.normSq ζ : ℂ) • Matrix.single j₀ j₀ (1 : ℂ) := by sorry
