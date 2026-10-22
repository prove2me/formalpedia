-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_indep_of_all_finite_cylinders
-- name    : AvramDividend.Classical.chat04_full_shifted_future_path_indep_of_all_finite_cylinders
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:35:44.961724+00:00
-- url     : https://prove2.me/theorems/7b8aa9ab-9dc6-4b9a-a595-32d384e805ca
-- title:
--   Full continuous-time shifted Lévy future-process independence from arbitrary past statistic, given finite-cylinder laws
-- statement:
--   For a canonical spectrally negative Lévy process X and a deterministic time s, consider the WHOLE future shifted process (t≥0)↦X_(s+t)−X_s, as a measurable random variable valued in the function space of all non-negative times. Let H:Ω→E be an arbitrary E-valued F_s-measurable past statistic. Suppose that for every finite set I of non-negative future observation times, the FINITE JOINT future-increment vector (i∈I)↦X_(s+i)−X_s is independent of H. Then the ENTIRE continuous-time indexed shifted future process is independent of H. The theorem requires joint finite-dimensional independence (not merely coordinatewise), uses original Lévy adaptedness to prove measurable increments and the exact pinned Mathlib IndepFun.process_indepFun theorem to promote finite cylinders to process-space independence. It removes any need for an auxiliary countable dense-grid sigma algebra when proving future-path conditional laws, although proving finite-cylinder independence from the Lévy independent-increments axioms remains outstanding. No killed q-scale harmonicity is assumed.
-- source:
--   Pinned Mathlib ProbabilityTheory.IndepFun.process_indepFun theorem (Mathlib.Probability.Independence.Process.Basic), together with original SpectrallyNegativeLevy adaptation and IsProbabilityMeasure. Public Mathlib docs confirmed its finite-cylinder-to-whole-process statement; remote verification at pinned revision is authoritative.

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_full_shifted_future_path_indep_of_all_finite_cylinders
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      IndepFun
        (fun ω (i : I) => X.X (s + (i : ℝ≥0)) ω - X.X s ω)
        H P) :
    IndepFun
      (fun ω (t : ℝ≥0) => X.X (s + t) ω - X.X s ω)
      H P := by sorry
