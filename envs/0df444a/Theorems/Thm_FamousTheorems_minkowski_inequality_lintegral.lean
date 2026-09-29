-- Prove2me | Theorems.Thm_FamousTheorems_minkowski_inequality_lintegral
-- name    : FamousTheorems.minkowski_inequality_lintegral
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:49.320382+00:00
-- url     : https://prove2.me/theorems/f0f15b3a-db71-474e-a38b-02c8aa70fa15
-- title:
--   Minkowski's inequality (integral form)
-- statement:
--   **Minkowski's inequality (integral form).** Let $\mu$ be a measure, $p\ge1$, and $f,g$ a.e.-measurable functions with values in $[0,\infty]$. Then
--   $$\Big(\int(f+g)^p\,d\mu\Big)^{1/p}\le\Big(\int f^p\,d\mu\Big)^{1/p}+\Big(\int g^p\,d\mu\Big)^{1/p}.$$
--
--   This is the triangle inequality for the $L^p$ norm, which makes $L^p$ a normed space for $p\ge1$. With counting measure it gives the triangle inequality for the $\ell^p$ norms on sequences and on $\mathbb R^n$.
--
--   **Formalization note.** Mathlib's `ENNReal.lintegral_Lp_add_le`. The functions take values in `ENNReal` and `∫⁻` is the lower Lebesgue integral, so no integrability hypothesis is needed. The exponent `p` is real and `^ (1 / p)` is the extended-real power.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ENNReal.lintegral_Lp_add_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem minkowski_inequality_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} {f g : α → ENNReal}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by sorry

end FamousTheorems
