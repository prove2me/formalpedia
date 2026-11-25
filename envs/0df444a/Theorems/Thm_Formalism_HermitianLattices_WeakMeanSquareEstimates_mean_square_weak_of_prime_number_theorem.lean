-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_WeakMeanSquareEstimates_mean_square_weak_of_prime_number_theorem
-- name    : Formalism.HermitianLattices.WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:43.995534+00:00
-- url     : https://prove2.me/theorems/1dc560eb-8865-4120-814d-59cfc9ed582b
-- title:
--   Weak Mean Square Estimates: mean square weak of prime number theorem
-- statement:
--   The Weak Mean Square Estimates construction uses the mean square weak of prime number theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/MeanSquareWeakOfPrimeNumberTheorem.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/MeanSquareWeakOfPrimeNumberTheorem.lean#L8-L10

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareOfPrimeNumberTheorem
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareWeakOfPrimeNumberTheorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeakMeanSquareEstimates

theorem Formalism.HermitianLattices.WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ MeanSquareHypW ε C x₀ := by sorry
