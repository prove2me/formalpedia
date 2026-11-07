-- Prove2me | Theorems.Thm_CubicProductLB_lemma_8
-- name    : CubicProductLB.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:56.206858+00:00
-- url     : https://prove2.me/theorems/5b4a1035-98b0-411e-a8b0-d4ea2157e0b6
-- title:
--   Lemma 8 — restricted bilinear estimate $|\mathbb E\chi(U + V + x^{\top}Ay)|^4 \le (3/4)^r$
-- statement:
--   Let $\chi(t) = \omega^t$ with $\omega = e^{2\pi i/3}$. Let $A$ be an invertible $r \times r$ matrix over $\mathbb F_3$, and let $U, V : \{-1,1\}^r \to \mathbb F_3$ be arbitrary functions. For independent uniform signs $x, y$,
--   $$\left| \mathbb E_{x,y}\, \chi\!\left( U(x) + V(y) + \sum_{i=1}^r x_i (Ay)_i \right) \right|^4 \le \left(\tfrac34\right)^r.$$
--   The estimate is the analytic input of the quadratic bias–rank statement: an invertible bilinear part forces the average to be small, whatever the terms in $x$ alone and in $y$ alone. The case $r = 0$ is included.
--
--   **Formalization Note** The character is `ZMod.stdAddChar`, and invertibility is that the determinant is a unit.
--
--   Differences from the source:
--   - encoding: U, V : {−1, 1}^r → F₃ → total functions on F₃^r; reason: only the values on the cube enter the average; same instances
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 8, Eq. (20), p.8

import Mathlib
import Definitions.Def_CubicProductLB_cubeAvg

namespace CubicProductLB

/-- Lemma 8 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 8, Eq. (20), p.8). For an invertible `r × r` matrix `A` over `F_3` and
arbitrary `U, V`, the bilinear average satisfies `|E_{x,y} χ(U(x) + V(y) + ∑_i x_i (Ay)_i)|^4 ≤ (3/4)^r`.

**Formalization Note** `χ` is `ZMod.stdAddChar`, `j ↦ e^{2πij/3}` (the `χ(t) = ω^t` of p.8). `U, V` are
total functions on `F_3^r`, only their values on the cube matter. `r = 0` is included. -/
theorem lemma_8 (r : ℕ) (A : Matrix (Fin r) (Fin r) (ZMod 3)) (hA : IsUnit A.det)
    (U V : (Fin r → ZMod 3) → ZMod 3) :
    ‖cubeAvg r fun x => cubeAvg r fun y =>
        ZMod.stdAddChar (U x + V y + ∑ i, x i * (A.mulVec y) i)‖ ^ 4 ≤ (3 / 4 : ℝ) ^ r := by sorry

end CubicProductLB
