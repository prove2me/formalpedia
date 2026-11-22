-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_Borel_mark_exponent_quantizers
-- name    : AvramDividend.Classical.avram_a77_original_finite_Borel_mark_exponent_quantizers
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:31:54.010202+00:00
-- url     : https://prove2.me/theorems/4c557e90-307d-4db4-b457-7915a2047972
-- title:
--   Original finite negative-jump Borel mark quantisers with physical step representation and deterministic intensity integral identity
-- statement:
--   Under finite negative original Levy activity, actual a.e. physical finite jump support, and original Borel count Poisson laws, construct a sequence of measurable negative Borel finite-step quantising exponent functions q_n tending pointwise on negative marks to theta*y, with q_n<=0. Their physically realised finite weighted negative-mark count sums f_n must be measurable, nonpositive a.e. and converge a.e. to theta times original J. The deterministic companion r_n must be both the exact finite partition rate sum and t times the integral of exp(q_n)-1 against original X.nu. This isolates the difficult simultaneous source bin partition and finite mark pathwise approximation. The deterministic rate convergence itself is supplied by a separate directly proved DCT lemma; no synthetic independent Poisson marks or assumed full Laplace conclusion.
-- source:
--   Avram root->a77 f4b58008->8bbaf3a8->5b48325d->cc5c4242. Derived using original full cc5 formal type, removing only deterministic dominated convergence and replacing it by exact q_n source integral identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_finite_Borel_mark_exponent_quantizers
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
    :
    ∃ (q : ℕ → ℝ → ℝ) (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (q n)) ∧
      (∀ n y, y < 0 → q n y ≤ 0) ∧
      (∀ y, y < 0 → Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) ∧
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
