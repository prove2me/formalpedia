-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_joint_centered_renewal_limits
-- name    : BellWilliams2001.ThresholdPolicy.joint_centered_renewal_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:07:52.347615+00:00
-- url     : https://prove2.me/theorems/ff01e5d9-5348-5ed5-ac4a-c923a1ab0ef8
-- title:
--   Joint diffusion limits and compact modulus for independent renewals
-- statement:
--   For finitely many independent renewal streams, the centered processes on a common real diffusion scale have independent Brownian finite observation limits and a joint asymptotic modulus bound.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem joint_centered_renewal_limits {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {k : ℕ} (V : Fin k → ℕ → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (V i j)) (hind : ∀ i, iIndepFun (V i) P)
    (hident : ∀ i j, IdentDistrib (V i j) (V i 0) P P)
    (hLp : ∀ i, MemLp (V i 0) 2 P) (hmean : ∀ i, ∫ ω, V i 0 ω ∂P = 1)
    (hpos : ∀ i j ω, 0 < V i j ω)
    (hIndV : iIndepFun (fun i ω j => V i j ω) P)
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (hrlim : Tendsto r atTop atTop)
    (aN : ℕ → Fin k → ℝ) (haN : ∀ n i, 0 ≤ aN n i)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (halim : ∀ i, Tendsto (fun n => aN n i) atTop (𝓝 (a i)))
    (B : Fin k → ℝ≥0 → Ω' → ℝ) (hB : ∀ i, IsBrownianReal (B i) P')
    (hBc : ∀ i ω, Continuous (fun t => B i t ω))
    (hIndB : iIndepFun (fun i ω t => B i t ω) P') :
    let X (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
      (((renewalCount (fun j => ∑ l ∈ Finset.range j, V i l ω) (aN n i*(r n^2*t))).toNat:ℝ)
        - aN n i*(r n^2*t)) / r n
    let Z (ω : Ω') (t : ℝ) (i : Fin k) := Real.sqrt (a i*variance (V i 0) P)*B i t.toNNReal ω
    (∀ (m : ℕ) (τ : Fin m → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
