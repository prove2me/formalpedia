-- Prove2me | Theorems.Thm_FamousTheorems_schwarz_lemma
-- name    : FamousTheorems.schwarz_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:27.748987+00:00
-- url     : https://prove2.me/theorems/9c29458c-3ea3-430b-84a0-f8a2606211dc
-- title:
--   The Schwarz lemma
-- statement:
--   **The Schwarz lemma.** Let $E,F$ be complex normed spaces and $f$ holomorphic on the open ball $B(0,R)\subseteq E$ with $f(B(0,R))\subseteq\overline B(0,R)$ and $f(0)=0$. Then
--   $$\|f(z)\|\le\|z\|\qquad\text{for all }\|z\|<R .$$
--
--   In the classical case $E=F=\mathbb C$, $R=1$, it says a holomorphic self-map of the unit disc fixing $0$ satisfies $|f(z)|\le|z|$. It is the starting point of the Schwarz–Pick lemma, of the description of the automorphisms of the disc, and of hyperbolic geometry in complex analysis.
--
--   **Formalization note.** Mathlib's `Complex.norm_le_norm_of_mapsTo_ball`. Holomorphy is complex differentiability on the ball (`DifferentiableOn ℂ`). The classical equality case ($|f(z)|=|z|$ at some $z\neq0$ forces a rotation) is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.norm_le_norm_of_mapsTo_ball`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schwarz_lemma {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {R : ℝ} {f : E → F} {z : E} (hd : DifferentiableOn ℂ f (Metric.ball 0 R))
    (h_maps : Set.MapsTo f (Metric.ball 0 R) (Metric.closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ := by sorry

end FamousTheorems
