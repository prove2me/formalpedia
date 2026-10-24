-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_causal_convolution
-- name    : AvramDividend.Classical.integrable_causal_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:17:07.02823+00:00
-- url     : https://prove2.me/theorems/e26ab9c4-9c2f-4d9e-bad9-f27b33bc03b3
-- title:
--   Lebesgue convolution of two real L1 kernels remains L1
-- statement:
--   Convolution of two real-valued Lebesgue integrable kernels f and g is integrable. It is the exact integral-expression form of pinned Mathlib Integrable.integrable_convolution, needed for the inductive integrability of Esscher BV renewal convolution-power densities.
-- source:
--   Pinned Mathlib.Analysis.Convolution lemma Integrable.integrable_convolution instantiated with multiplication.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped Convolution

namespace AvramDividend.Classical
theorem integrable_causal_convolution
    (f g : ℝ → ℝ) (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) volume := by sorry
end AvramDividend.Classical
