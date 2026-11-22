-- Prove2me | Theorems.Thm_BornVolume_born_frequencies_tendsto_born_weights
-- name    : BornVolume.born_frequencies_tendsto_born_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:21.770515+00:00
-- url     : https://prove2.me/theorems/6307a9c2-5930-4d17-8d63-249b26088eb3
-- title:
--   Born Volume: born frequencies tendsto born weights
-- statement:
--   **Invariant sampling reproduces the Born weights as long-run frequencies.** Let `μ` be a
--   unitarily invariant probability measure on `ℂℙᴹ`, `ψ` a unit vector of `ℂᴹ⁺¹`, and `X n`
--   pairwise independent random states, each with law `μ`. Almost surely, for every outcome `i`, the
--   fraction of the first `m` states lying in the Born cell `bornCell ψ i` tends to the Born weight
--   `‖ψᵢ‖²` as `m → ∞`. The cells depend on `ψ`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L156-L192
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L156-L192

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.born_frequencies_tendsto_born_weights (μ : Measure (CPN (M + 1)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = μ)
    (hindep : Pairwise fun m n => IndepFun (X m) (X n) Pr) :
    ∀ᵐ ω ∂Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m, Set.indicator (bornCell ψ i) (fun _ => (1 : ℝ)) (X k ω))
            / (m : ℝ))
        atTop (nhds (‖ψ i‖ ^ 2)) := by sorry
