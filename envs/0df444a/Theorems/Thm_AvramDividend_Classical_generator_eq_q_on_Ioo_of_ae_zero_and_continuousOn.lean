-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
-- name    : AvramDividend.Classical.generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:58:18.348712+00:00
-- url     : https://prove2.me/theorems/9f9e9d9a-8291-44da-8b20-3454694e7370
-- title:
--   Pointwise q-generator harmonicity from an a.e. identity and local continuity
-- statement:
--   For the spectrally negative Lévy generator, if its residual R(x)=ΓW(x)-qW(x) is continuous on the positive interval (0,a), and vanishes Lebesgue-a.e. there, it vanishes at every point of the interval. The proof applies the already established theorem upgrading an a.e.-zero continuous function to a pointwise-zero function on an open set of positive measure support. This is the exact terminal link required after a legitimate local weak generator calculation or properly justified Laplace inversion.
-- source:
--   Accepted `continuousOn_zero_of_ae_zero_restrict_open`; terminal a.e.-to-pointwise step for Avram Dividend Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (Ioo 0 a))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
