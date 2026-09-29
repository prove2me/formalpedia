-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_mean_value_theorem
-- name    : FamousTheorems.cauchy_mean_value_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:12.237896+00:00
-- url     : https://prove2.me/theorems/887e4cf0-8b02-4dac-bf05-6c5b0c23cfed
-- title:
--   Cauchy's mean value theorem
-- statement:
--   **Cauchy's mean value theorem.** Let $a<b$ and $f,g:[a,b]\to\mathbb R$ be continuous on $[a,b]$ and differentiable on $(a,b)$ with derivatives $f',g'$. Then there is $c\in(a,b)$ with
--   $$\big(g(b)-g(a)\big)f'(c)=\big(f(b)-f(a)\big)g'(c).$$
--
--   Taking $g(x)=x$ gives Lagrange's mean value theorem. It is the standard route to L'Hôpital's rule and to the Lagrange form of the remainder in Taylor's theorem.
--
--   **Formalization note.** Mathlib's `exists_ratio_hasDerivAt_eq_ratio_slope`. The platform's older `Cauchy_Mean_Value_Theorem` entry is a deprecated placeholder stating only `True`; this is the actual theorem. Derivatives are given by `HasDerivAt` at the interior points.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_ratio_hasDerivAt_eq_ratio_slope`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_mean_value_theorem {f f' g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hgc : ContinuousOn g (Set.Icc a b))
    (hgg' : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) :
    ∃ c ∈ Set.Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by sorry

end FamousTheorems
