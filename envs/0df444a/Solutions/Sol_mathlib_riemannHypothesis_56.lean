-- Prove2me | solution 56 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:19.056087+00:00
-- url     : https://prove2.me/submissions/e4557010-1bc0-4119-ae2f-be865ecd39cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_lower_bound
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloAudit_trace_formula_rational_one_sided_window_iff
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloAudit_one_sided_regular_windows_iff_RH

-- Step 1: `MasulloRH.rational_theta_cutoff_trace_lower_bound` implies `MasulloRH.cofinal_one_sided_trace_windows` (accepted reduction of `MasulloRH.cofinal_one_sided_trace_windows`).
section

open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology

theorem MasulloRH.cofinal_one_sided_trace_windows (n : ℕ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / (n + 1 : ℝ) ∧
      ∀ φ : ℝ → ℂ, IsRationalTraceTest φ → tsupport φ ⊆ Ioi 1 →
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1/2) + mellin φ (-1/2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  classical
  have existsT (j : ℕ) : ∃ T : rationalThetaAnnihilator ((j:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((j:ℝ)+1),
      IsRationalThetaConvolution ((j:ℝ)+1) (regularizedTraceTest j 3) T := by
    obtain ⟨T,hT,_⟩ := (rational_theta_annihilator_jet_trace ((j:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) j])).2 _ (regularized_test_admissible j 3)
    exact ⟨T,hT.1⟩
  choose T hT using existsT
  let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
    (zeroResolventTerm (1/2) 3 z.val).re
  obtain ⟨hlim,hpos,hiff⟩ := rational_theta_cutoff_trace_defect T hT
  have hnonpos : D ≤ 0 := by
    by_contra! hD
    have he : 0 < D/2 := by linarith
    have hlarge := (tendsto_order.mp hlim).1 (D/2) (show D/2 < D by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.1 hlarge
    obtain ⟨j,hj,hjT⟩ := rational_theta_cutoff_trace_lower_bound (D/2) he N
    have hu := hjT (T j) (hT j)
    have hl := hN j hj
    linarith
  have hRH : RiemannHypothesis := hiff.mp (le_antisymm hnonpos hpos)
  let α := 1 / (n+1:ℝ)
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨α,hα,le_rfl,fun φ hφ hsupport => ?_⟩
  have hline (ρ : ZetaZerosInTraceStrip (1/2)) : |ρ.val.re - 1/2| < α := by
    have h := riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH ρ.val
      ρ.property.1 ρ.property.2.1 ρ.property.2.2.1
    simpa [h] using hα
  exact ((MasulloAudit.trace_formula_rational_one_sided_window_iff α hα).2 hline φ hφ hsupport).2.2.2

end

-- Step 2: `MasulloRH.cofinal_one_sided_trace_windows` implies `MasulloRH.regular_width_one_sided_trace` (accepted reduction of `MasulloRH.regular_width_one_sided_trace`).
section

-- New proof-sketch for the Masullo mission's regular-width frontier.




open MasulloRH MeasureTheory Set Filter Topology

theorem MasulloRH.regular_width_one_sided_trace (β : ℝ) (hβ : 0 < β)
    (hreg : ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| ≠ β)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (hpos : tsupport φ ⊆ Ioi 1) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1/2) + mellin φ (-1/2) -
        ∑' ρ : ZetaZerosInTraceStrip β, zetaTraceTerm φ β ρ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hβ
  obtain ⟨α, ha, han, htrace⟩ := cofinal_one_sided_trace_windows n
  have inside := (MasulloAudit.trace_formula_rational_one_sided_window_iff α ha).mp
    (fun f hf hs ↦ by
      have c := trace_window_comparison α f hf
      exact ⟨c.1, c.2.1, c.2.2.1, htrace f hf hs⟩)
  have wider := (MasulloAudit.trace_formula_rational_one_sided_window_iff β hβ).mpr
    (fun ρ ↦ (inside ρ).trans (lt_of_le_of_lt han hn))
  exact (wider φ hφ hpos).2.2.2

end

-- Step 3: `MasulloRH.regular_width_one_sided_trace` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloAudit.one_sided_regular_windows_iff_RH.mp
    (fun β hβ hreg φ hφ hpos =>
      MasulloRH.regular_width_one_sided_trace β hβ hreg φ hφ hpos)

end
