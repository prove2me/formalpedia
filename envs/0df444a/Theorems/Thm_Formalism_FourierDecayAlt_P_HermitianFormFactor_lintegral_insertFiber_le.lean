-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lintegral_insertFiber_le
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_insertFiber_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:27.116008+00:00
-- url     : https://prove2.me/theorems/80ad52c0-db96-4539-8147-41150f27ccf8
-- title:
--   Hermitian Form Factor: lintegral insert Fiber le
-- statement:
--   The Hermitian Form Factor construction uses the lintegral insert Fiber le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L637-L681
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L637-L681

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_insertFiber_le (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (X : Q → Q → ℂ) (j₀ : Q) (n : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (w : Q → ℂ) :
    ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n)) - Matrix.single j₀ j₀ (1 : ℂ)) =
      ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n))) := by sorry
