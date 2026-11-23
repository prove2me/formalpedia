-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_simpleFunc_physical_mark_count_reconstruction
-- name    : AvramDividend.Classical.avram_a77_original_simpleFunc_physical_mark_count_reconstruction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:38:33.233807+00:00
-- url     : https://prove2.me/theorems/db0a17f3-92f2-4e30-bad7-2657b90157e6
-- title:
--   Original physical finite Borel negative-mark count reconstruction from an arbitrary nonpositive simple-function quantiser
-- statement:
--   Given an explicit finite-range strongly measurable negative-mark SimpleFunc q_n with q_n<=0 and q_n(y) tending to theta*y for all negative marks, and the original spectrally negative Lévy source X with finite negative jump support and all Borel Poisson count representatives, reconstruct measurable physical finite-step count exponents f_n and deterministic source intensity exponent integrals r_n. Show f_n<=0 a.e. and f_n tends a.e. to theta times the actual physical signed jump sum J; for each n, the exact step f_n must equal the source marked count weighted sum on some finite pairwise disjoint negative Borel partition and r_n the corresponding source Lévy-intensity weighted finite sum as well as t*integral(exp(q_n)-1). This requires genuine source marked-count fibre arithmetic and finite support, not the generic quantisation or DCT already Proved.
-- source:
--   Avram original finite negative jump Laplace a77->8bb->5b->cc5->4c source mark quantiser after removing standalone generic SimpleFunc quantisation. Keep all source sample-law constraints unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_simpleFunc_physical_mark_count_reconstruction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (q : ℕ → SimpleFunc ℝ ℝ)
    (hNonpos : ∀ n y, q n y ≤ 0)
    (hPointwise : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    ∃ (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (θ * J ω))) ∧
      (∀ n, r n = (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂X.ν)) ∧
      ∀ n : ℕ, ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f n ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r n = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by sorry
