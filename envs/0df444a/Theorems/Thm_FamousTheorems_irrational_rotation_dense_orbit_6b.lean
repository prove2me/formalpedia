-- Prove2me | Theorems.Thm_FamousTheorems_irrational_rotation_dense_orbit_6b
-- name    : FamousTheorems.irrational_rotation_dense_orbit_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:59.851262+00:00
-- url     : https://prove2.me/theorems/1efe14bc-b007-4ac6-b1f3-9bf24ee05555
-- title:
--   Irrational rotations of the circle have dense orbits
-- statement:
--   **Irrational rotations of the circle have dense orbits.** Let $p$ be a real number and let $\mathbb R/p\mathbb Z$ be the circle of length $p$. For $a\in\mathbb R$, the set $\{na \bmod p:n\in\mathbb Z\}$ is dense in the circle if and only if $a/p$ is irrational.
--
--   Rotation of the circle by an irrational fraction of a full turn is the basic example of a minimal dynamical system: every orbit is dense. This fact is the starting point of Weyl's equidistribution theorem and of the theory of rotation numbers, and it has applications in Diophantine approximation.
--
--   **Formalization note.** Mathlib's `AddCircle.denseRange_zsmul_coe_iff`. `AddCircle p` is $\mathbb R/p\mathbb Z$, and the orbit is the range of $n\mapsto n\cdot\bar a$ for $n\in\mathbb Z$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AddCircle.denseRange_zsmul_coe_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem irrational_rotation_dense_orbit_6b {a p : ℝ} : (DenseRange fun n : ℤ => n • (a : AddCircle p)) ↔ Irrational (a / p) := by sorry

end FamousTheorems
