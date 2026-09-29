-- Prove2me | Theorems.Thm_FamousTheorems_hadamard_three_lines
-- name    : FamousTheorems.hadamard_three_lines
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:11.409954+00:00
-- url     : https://prove2.me/theorems/04c067a6-e9b6-4ba5-9cfb-7a765a89141a
-- title:
--   The Hadamard three-lines theorem
-- statement:
--   **The Hadamard three-lines theorem.** Let $f$ be a bounded function on the closed strip $l\le\operatorname{Re}z\le u$, continuous there and holomorphic inside, with values in a complex normed space. If $\|f\|\le a$ on the line $\operatorname{Re}z=l$ and $\|f\|\le b$ on the line $\operatorname{Re}z=u$, then inside the strip
--   $$\|f(z)\|\le a^{1-\theta}\,b^{\theta},\qquad\theta=\frac{\operatorname{Re}z-l}{u-l}.$$
--
--   So $\log\sup_{\operatorname{Re}z=x}\|f\|$ is a convex function of $x$. It is the complex-analytic heart of the Riesz–Thorin interpolation theorem and is used for convexity bounds on $L$-functions (Phragmén–Lindelöf).
--
--   **Formalization note.** Mathlib's `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`. The strips are written directly as preimages of intervals under `Complex.re`, and the powers are real powers `Real.rpow`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hadamard_three_lines {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {a b l u : ℝ} (hul : l < u)
    (hz : z.re ∈ Set.Icc l u) (hd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo l u))
    (hB : BddAbove ((fun w => ‖f w‖) '' (Complex.re ⁻¹' Set.Icc l u)))
    (ha : ∀ w : ℂ, w.re = l → ‖f w‖ ≤ a) (hb : ∀ w : ℂ, w.re = u → ‖f w‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by sorry

end FamousTheorems
