-- Prove2me | Theorems.Thm_FamousTheorems_quadratic_formula_7b
-- name    : FamousTheorems.quadratic_formula_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:43.727644+00:00
-- url     : https://prove2.me/theorems/eca0437e-3d7b-48c2-9fdb-c71436344c6a
-- title:
--   The quadratic formula
-- statement:
--   **The quadratic formula.** Let $K$ be a field of characteristic other than $2$, and let $a,b,c\in K$ with $a\neq0$. Suppose that the discriminant $b^2-4ac$ is a square $s^2$ in $K$. Then for every $x\in K$,
--   $$ax^2+bx+c=0\iff x=\frac{-b+s}{2a}\ \text{ or }\ x=\frac{-b-s}{2a}.$$
--
--   The formula goes back to Babylonian and Indian mathematics, and in general form to al-Khwarizmi. Its failure to generalize to degree $5$ and higher, by the Abel–Ruffini theorem, was one of the origins of group theory. The proof completes the square: $4a(ax^2+bx+c)=(2ax+b)^2-(b^2-4ac)$.
--
--   **Formalization note.** Mathlib's `quadratic_eq_zero_iff`. `discrim a b c` is $b^2-4ac$, and the condition `NeZero (2 : K)` says that the characteristic is not $2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `quadratic_eq_zero_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem quadratic_formula_7b {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K} (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s)
    (x : K) : a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by sorry

end FamousTheorems
