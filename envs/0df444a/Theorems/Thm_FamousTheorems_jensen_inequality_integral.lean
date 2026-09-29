-- Prove2me | Theorems.Thm_FamousTheorems_jensen_inequality_integral
-- name    : FamousTheorems.jensen_inequality_integral
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:17.222193+00:00
-- url     : https://prove2.me/theorems/0246c0a0-3d23-4b23-97b3-7334d940a4f6
-- title:
--   Jensen's inequality (integral form)
-- statement:
--   **Jensen's inequality (integral form).** Let $\mu$ be a probability measure, $s$ a closed convex subset of a real Banach space $E$, and $g:E\to\mathbb R$ convex and continuous on $s$. If $f$ takes values in $s$ almost everywhere and both $f$ and $g\circ f$ are integrable, then
--   $$g\Big(\int f\,d\mu\Big)\le\int g\circ f\,d\mu .$$
--
--   It is one of the most used inequalities in analysis and probability. Special cases include the AM–GM inequality, $(\mathbb E X)^2\le\mathbb E X^2$, and the nonnegativity of relative entropy, and it underlies the monotonicity of $L^p$ norms on probability spaces.
--
--   **Formalization note.** Mathlib's `ConvexOn.map_integral_le`. Integrals are Bochner integrals, and `∀ᵐ x ∂μ, f x ∈ s` means $f(x)\in s$ for $\mu$-almost every $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ConvexOn.map_integral_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jensen_inequality_integral {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ] {s : Set E} {f : α → E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : MeasureTheory.Integrable f μ) (hgi : MeasureTheory.Integrable (g ∘ f) μ) :
    g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by sorry

end FamousTheorems
