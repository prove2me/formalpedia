-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_q_harmonic_of_common_root
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_q_harmonic_of_common_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:38:41.01648+00:00
-- url     : https://prove2.me/theorems/5d993efc-b0ac-4412-badf-23b2593e7928
-- title:
--   Every finite signed original Lévy q-eigenexponential family is in the full generator domain and pointwise q-harmonic
-- statement:
--   Let F be an arbitrary finite signed real sum of original spectrally negative Lévy exponential functions exp(theta_i x) with theta_i≥0, all sharing the exact Lévy exponent eigenvalue ψ(theta_i)=q. Then F lies in the true compensated Lévy jump-generator domain and ΓF(x)-qF(x)=0 at every x. The proof uses exact nonlocal generator linearity and the Lévy–Khintchine eigenfunction equation, including drift, Gaussian and compensated negative-jump terms. It supports authentic finite-test martingale/Dynkin reasoning without claiming stopped q-scale harmonicity.
-- source:
--   New Proved exact full generator finite-family linearity dd86b696 and Proved original exponential generator eigenvalue identity e651bf0f.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_linear
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_q_harmonic_of_common_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) (hroot : ∀ i ∈ s, X.ψ (rate i) = q) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    X.generator
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x -
        q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)) = 0 := by sorry
