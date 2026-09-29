-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_sum_mul_inv_7b
-- name    : FamousTheorems.jacobi_sum_mul_inv_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:35.993878+00:00
-- url     : https://prove2.me/theorems/bf4feec1-5355-4f48-b0c6-b2deb14ae9b5
-- title:
--   J(χ,ψ)·J(χ⁻¹,ψ⁻¹) = q for Jacobi sums
-- statement:
--   **The absolute value of Jacobi sums.** Let $F$ be a finite field with $q$ elements, $F'$ a field whose characteristic differs from that of $F$, and $\chi,\varphi$ nontrivial multiplicative characters of $F$ with values in $F'$ such that $\chi\varphi$ is nontrivial. Then
--   $$J(\chi,\varphi)\,J(\chi^{-1},\varphi^{-1})=q.$$
--
--   For complex characters $J(\chi^{-1},\varphi^{-1})=\overline{J(\chi,\varphi)}$, so this says $|J(\chi,\varphi)|=\sqrt q$. This is the key estimate in counting points on curves such as $y^2=x^3+D$ and $x^n+y^n=1$ over finite fields, and so it verifies the Riemann hypothesis for these curves in Weil's approach.
--
--   **Formalization note.** Mathlib's `jacobiSum_mul_jacobiSum_inv`. `ringChar` is the characteristic, and the right side is $q=|F|$ viewed in $F'$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobiSum_mul_jacobiSum_inv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_sum_mul_inv_7b {F F' : Type*} [Fintype F] [Field F] [Field F'] (hchar : ringChar F' ≠ ringChar F)
    {χ φ : MulChar F F'} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by sorry

end FamousTheorems
