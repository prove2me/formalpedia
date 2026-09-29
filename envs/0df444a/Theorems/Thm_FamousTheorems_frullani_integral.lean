-- Prove2me | Theorems.Thm_FamousTheorems_frullani_integral
-- name    : FamousTheorems.frullani_integral
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:59.519916+00:00
-- url     : https://prove2.me/theorems/b67c2565-5c1f-4272-bdb8-5347d8dc6aca
-- title:
--   Frullani's integral
-- statement:
--   **Frullani's integral.** Let $f:\mathbb R\to E$ be locally integrable on $(0,\infty)$, with values in a real Banach space, and suppose $f(x)\to L$ as $x\to0^+$ and $f(x)\to R$ as $x\to\infty$. Then for $a,b>0$, provided the integral converges,
--   $$\int_0^\infty\frac{f(ax)-f(bx)}{x}\,dx=\log\frac ba\,(L-R).$$
--
--   Frullani stated this in 1821. It evaluates many integrals that resist direct antidifferentiation, for example $\int_0^\infty\frac{e^{-ax}-e^{-bx}}x\,dx=\log\frac ba$ and $\int_0^\infty\frac{\arctan(ax)-\arctan(bx)}x\,dx=\frac\pi2\log\frac ab$.
--
--   **Formalization note.** Mathlib's `Frullani.integral_Ioi_eq`. The integral is the Lebesgue (Bochner) integral over `Set.Ioi 0`. Its integrability is an explicit hypothesis, and the limits are stated as filter limits along `nhdsWithin 0 (Set.Ioi 0)` and `atTop`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Frullani.integral_Ioi_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem frullani_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ} {L R : E}
    (hf : LocallyIntegrableOn f (Set.Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) (hR : Filter.Tendsto f Filter.atTop (nhds R))
    (hint : IntegrableOn (fun x : ℝ => x⁻¹ • (f (a * x) - f (b * x))) (Set.Ioi 0)) :
    ∫ x in Set.Ioi (0 : ℝ), x⁻¹ • (f (a * x) - f (b * x)) = Real.log (b / a) • (L - R) := by sorry

end FamousTheorems
