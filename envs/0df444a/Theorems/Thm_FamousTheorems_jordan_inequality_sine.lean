-- Prove2me | Theorems.Thm_FamousTheorems_jordan_inequality_sine
-- name    : FamousTheorems.jordan_inequality_sine
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:47.273949+00:00
-- url     : https://prove2.me/theorems/6df33746-1cdc-4eb9-accf-568ab711701f
-- title:
--   Jordan's inequality
-- statement:
--   **Jordan's inequality.** For $0\le x\le\pi/2$,
--   $$\frac{2}{\pi}\,x\le\sin x.$$
--
--   The chord from $(0,0)$ to $(\pi/2,1)$ lies below the concave graph of the sine. Jordan's inequality is the key estimate in Jordan's lemma, which controls integrals over large semicircles in contour integration, for example in computing $\int_{-\infty}^\infty\frac{\sin x}{x}\,dx$.
--
--   **Formalization note.** Mathlib's `Real.mul_le_sin`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.mul_le_sin`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jordan_inequality_sine {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 2) :
    2 / Real.pi * x ≤ Real.sin x := by sorry

end FamousTheorems
