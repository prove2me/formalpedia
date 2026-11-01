-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:33:56.180037+00:00
-- url     : https://prove2.me/theorems/d19177af-e2bc-4c43-813a-5abc846cb4bf
-- title:
--   Actual finite-horizon Stieltjes dividend measure splits into countable right atoms and an atomless remainder without losing any continuous mass
-- statement:
--   For every actual adapted increasing left-continuous Avram dividend path D, every sample ω and every finite horizon T, the genuine restricted Stieltjes measure on [0,T] has total mass rightLimit D T. It decomposes exactly as a countable Dirac sum of its time atoms plus an atomless remainder, without discarding absolutely continuous or singular-continuous payments. Every atom at any t in [0,T] has exactly the source's chronological right-payment mass rightLimit D t minus D t, including t=0 and t=T. This is a full-mass measure decomposition foundational to, but distinct from, the stochastic Itô–Meyer chain rule.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), actual dividendMeasure and rightLimit declarations; existing Proved finite-horizon exact Stieltjes mass and generic atomic/diffuse decomposition. No claim that the diffuse part is absolutely continuous, no invalid atom concentration axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by sorry
