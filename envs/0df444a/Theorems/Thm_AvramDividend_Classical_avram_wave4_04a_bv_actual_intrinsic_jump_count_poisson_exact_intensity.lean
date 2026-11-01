-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:55:29.461611+00:00
-- url     : https://prove2.me/theorems/237842ca-64a3-4f7b-9393-9d2c19284771
-- title:
--   Actual BV finite-negative-activity original Lévy jump count has exact Poisson(Tν) law
-- statement:
--   For the genuine bounded-variation finite-negative-activity spectrally negative Lévy source X on its original probability space P and all T>0, its literal original-path intrinsic jump counting measure N_X((0,T]×ℝ) has a complete Poisson distribution with explicit rate T*X.ν((−∞,0)). No external grid or scaling hypotheses remain. The proof constructs deterministic uniform partitions, invokes a verified original-source grid count law, and proves the rare-event rate convergence via the derivative of exp. It preserves original paths and does not assert an arbitrary marked-band compensator.
-- source:
--   Original-source BV pathwise count and grid scaling theorem 63f4aa92-41c6-45ac-9e21-929b65c7796c is canonically Proved. New exact source negative-intensity uniform-grid rate c7c5e30d-0135-4f04-aca8-396bd7519f1a is published and proof candidate 20310 pending at authoring time; do not import it as Proved until accepted. Construct step(n)=T/(n:NNReal), grid(n,i)=i*step(n), prove monotonicity, strictness for n>0, endpoints 0/T, width identity, uniform mesh→0, and rate n(1−e^(−step(n)ν))→Tν. Apply 63f4 to the literal original N_X and its exact source intensity. No auxiliary Poisson process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (k : ℕ) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal)} =
      Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) *
        ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) ^ k /
          (k.factorial : ℝ) := by sorry
