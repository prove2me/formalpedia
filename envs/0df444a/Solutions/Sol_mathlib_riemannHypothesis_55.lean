-- Prove2me | solution 55 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:17.756284+00:00
-- url     : https://prove2.me/submissions/4a9f3681-9ea1-4c73-83ef-553a9651fd49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_omitted_spectral_mass_zero
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable
import Theorems.Thm_MasulloRH_primePowerTraceTerm_finite_support
import Mathlib.Tactic.Abel
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH

-- Step 1: `MasulloRH.omitted_spectral_mass_zero` implies `MasulloRH.spectral_trace_hasSum` (accepted reduction of `MasulloRH.spectral_trace_hasSum`).
section

open MeasureTheory Set
open MasulloRH

theorem MasulloRH.spectral_trace_hasSum (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  obtain ⟨-, -, hS, -, hEq⟩ := MasulloAudit.trace_formula_window_with_remainder α φ hφ
  -- The remainder of the unconditional window formula is the omitted zero sum, re-indexed.
  let e : {z : {w : ℂ // ConnesRZ.IsCriticalZero w} // ¬ |z.val.re - 1/2| < α} ≃
      {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|} :=
    { toFun := fun r =>
        ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2,
          by rw [abs_lt]; constructor <;> linarith [r.1.2.2.1, r.1.2.2.2]⟩, not_lt.1 r.2⟩
      invFun := fun r =>
        ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2.1⟩, not_lt.2 r.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hrem : (∑' ρ : {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|},
      zetaTraceTerm φ (1 / 2) ρ) = 0 := by
    rw [← e.tsum_eq]
    exact MasulloRH.omitted_spectral_mass_zero α hα φ hφ
  rw [hrem, sub_zero] at hEq
  have : (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) =
      (mellin φ (1 / 2) + mellin φ (-1 / 2)) -
        ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
          ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) := by
    rw [hEq]; ring
  rw [← this]
  exact hS.hasSum

end

-- Step 2: `MasulloRH.spectral_trace_hasSum` implies `MasulloRH.trace_formula_rational` (accepted reduction of `MasulloRH.trace_formula_rational`).
section

open MasulloRH MeasureTheory Set

theorem MasulloRH.trace_formula_rational (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  have h := spectral_trace_hasSum α hα φ hφ
  refine ⟨realTraceIntegrand_integrable φ hφ,
    summable_of_hasFiniteSupport (primePowerTraceTerm_finite_support φ hφ), h.summable, ?_⟩
  rw [h.tsum_eq]
  abel

end

-- Step 3: `MasulloRH.trace_formula_rational` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.trace_formula_rational_iff_RH.mp
    (fun α hα φ hφ => MasulloRH.trace_formula_rational α hα φ hφ)

end
