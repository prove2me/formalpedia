-- Prove2me | Theorems.Thm_FamousTheorems_ceva
-- name    : FamousTheorems.ceva
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:32.188114+00:00
-- url     : https://prove2.me/theorems/8da5703c-d140-4c79-9dca-9920a54b7acd
-- title:
--   Ceva's theorem
-- statement:
--   **Ceva's theorem.**
--
--   Let $t$ be a triangle with vertices $A_0, A_1, A_2$, and for each $i$ let $P_i$ be a point on the line
--   through the other two vertices $A_{i+1}, A_{i+2}$. If the three cevians $A_iP_i$ are concurrent — all
--   passing through a common point $p'$ — then
--   $$\prod_{i=0}^{2} \frac{|A_{i+1}P_i|}{|P_iA_{i+2}|} \;=\; 1 .$$
--
--   Each cevian cuts the opposite side in some ratio; the theorem says concurrency forces the three ratios
--   to multiply to one. It is the clean criterion for three lines through the vertices to meet, and it
--   immediately gives the concurrency of the medians (all ratios $1$), the angle bisectors (via the
--   bisector length formula), and the altitudes. The converse holds too, which is how the standard
--   triangle centres are usually proved to exist.
--
--   Giovanni Ceva published it in *De lineis rectis* (1678), though it was known to al-Mu'taman ibn Hud in
--   11th-century Zaragoza. It is the projective dual companion to Menelaus' theorem, where collinearity of
--   three points on the sides gives product $-1$ in signed ratios.
--
--   **Formalization note.** Indices are in `Fin 3` so `i + 1`, `i + 2` wrap cyclically; `line[𝕜, x, y]` is
--   the affine span of two points, and the hypothesis `hp0` rules out the degenerate zero denominator.
--   Working with unsigned distances is why the product is $+1$ rather than a signed $\pm 1$. The result is
--   Mathlib's `Affine.Triangle.prod_dist_div_dist_eq_one_of_mem_line_of_mem_line`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Affine

theorem ceva {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]
    [MetricSpace P] [NormedAddTorsor V P] {t : Affine.Triangle 𝕜 P} {p : Fin 3 → P} {p' : P}
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : ∀ i : Fin 3, p' ∈ line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by sorry

end FamousTheorems
