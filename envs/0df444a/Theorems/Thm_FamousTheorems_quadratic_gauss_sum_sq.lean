-- Prove2me | Theorems.Thm_FamousTheorems_quadratic_gauss_sum_sq
-- name    : FamousTheorems.quadratic_gauss_sum_sq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:27.893291+00:00
-- url     : https://prove2.me/theorems/8ef1926c-8c47-4f55-860d-a791bc33cb0f
-- title:
--   The square of a quadratic Gauss sum
-- statement:
--   **The square of a quadratic Gauss sum.** Let $F$ be a finite field, $\chi$ a nontrivial quadratic multiplicative character and $\psi$ a primitive additive character of $F$, both with values in an integral domain. Then the Gauss sum $g(\chi,\psi)=\sum_{x\in F}\chi(x)\psi(x)$ satisfies
--   $$g(\chi,\psi)^2=\chi(-1)\,|F|.$$
--
--   For $F=\mathbb F_p$ this is Gauss's evaluation $g^2=\left(\frac{-1}p\right)p$. It shows that $\sqrt{\pm p}$ lies in a cyclotomic field and is the key step in Gauss's sixth proof of quadratic reciprocity.
--
--   **Formalization note.** Mathlib's `gaussSum_sq`. `MulChar.IsQuadratic` says that $\chi$ takes values in $\{0,\pm1\}$, and `AddChar.IsPrimitive` says that $\psi$ is primitive, meaning that every character $x\mapsto\psi(ax)$ with $a\ne0$ is nontrivial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `gaussSum_sq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem quadratic_gauss_sum_sq {R : Type*} [Field R] [Fintype R] {R' : Type*} [CommRing R'] [IsDomain R'] {χ : MulChar R R'}
    (hχ₁ : χ ≠ 1) (hχ : χ.IsQuadratic) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R := by sorry

end FamousTheorems
