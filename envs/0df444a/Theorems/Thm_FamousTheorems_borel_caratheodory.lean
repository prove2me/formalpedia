-- Prove2me | Theorems.Thm_FamousTheorems_borel_caratheodory
-- name    : FamousTheorems.borel_caratheodory
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:53.747157+00:00
-- url     : https://prove2.me/theorems/6ecb9f49-18d8-4dc7-8324-54074971e23c
-- title:
--   The Borel–Carathéodory theorem
-- statement:
--   **The Borel–Carathéodory theorem.** Let $f$ be holomorphic on the disc $|z|<R$ with $\operatorname{Re}f\le M$ there, where $M>0$. Then for $|z|<R$
--   $$|f(z)|\le\frac{2M|z|}{R-|z|}+|f(0)|\,\frac{R+|z|}{R-|z|}.$$
--
--   An upper bound on the real part alone controls the modulus. This is a standard lemma in complex analysis and analytic number theory, used to bound $\log\zeta$ and $\zeta'/\zeta$ and in the proof of Hadamard's factorisation theorem.
--
--   **Formalization note.** Mathlib's `Complex.borelCaratheodory`, with the hypothesis $\operatorname{Re}f\le M$ written as `Set.MapsTo f (ball 0 R) {w | w.re ≤ M}`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.borelCaratheodory`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem borel_caratheodory {f : ℂ → ℂ} {M R : ℝ} {z : ℂ} (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hfM : Set.MapsTo f (Metric.ball 0 R) {w : ℂ | w.re ≤ M}) (hR : 0 < R) (hz : z ∈ Metric.ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by sorry

end FamousTheorems
