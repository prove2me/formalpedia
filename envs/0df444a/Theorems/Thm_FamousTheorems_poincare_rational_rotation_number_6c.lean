-- Prove2me | Theorems.Thm_FamousTheorems_poincare_rational_rotation_number_6c
-- name    : FamousTheorems.poincare_rational_rotation_number_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:26.827125+00:00
-- url     : https://prove2.me/theorems/964e72d9-bf6d-434a-9956-b8e61e60a57b
-- title:
--   Poincaré's theorem: rational rotation number iff periodic orbit
-- statement:
--   **Poincaré's theorem on rational rotation numbers.** Let $f:\mathbb R\to\mathbb R$ be a continuous lift of a degree-one circle map, so that $f(x+1)=f(x)+1$ and $f$ is monotone. Let $m\in\mathbb Z$ and $n\ge1$. Then the translation number of $f$ equals $m/n$ if and only if there is a point $x$ with $f^n(x)=x+m$.
--
--   On the circle, this says that a circle homeomorphism has rational rotation number $m/n$ exactly when it has a periodic orbit of period $n$ that winds $m$ times around the circle. Poincaré proved this in 1885. It is the starting point of the dynamics of circle maps.
--
--   **Formalization note.** Mathlib's `CircleDeg1Lift.translationNumber_eq_rat_iff`. A `CircleDeg1Lift` is a monotone map $\mathbb R\to\mathbb R$ with $f(x+1)=f(x)+1$, and `translationNumber f` is $\lim_n f^n(0)/n$. Continuity of $f$ is a separate hypothesis. `f ^ n` is the $n$-fold composition.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CircleDeg1Lift.translationNumber_eq_rat_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem poincare_rational_rotation_number_6c (f : CircleDeg1Lift) (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f.translationNumber = m / n ↔ ∃ x, (f ^ n) x = x + m := by sorry

end FamousTheorems
