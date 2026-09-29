-- Prove2me | Theorems.Thm_FamousTheorems_fderiv_mul
-- name    : FamousTheorems.fderiv_mul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:13.440353+00:00
-- url     : https://prove2.me/theorems/c8611840-b0ac-41f5-94b2-b5a601ac3510
-- title:
--   The Leibniz rule for the Fréchet derivative
-- statement:
--   **The Leibniz rule** in the Frechet setting. For maps into a normed algebra, $$D(cd)(x)\,h = Dc(x)h \cdot d(x) + c(x)\cdot Dd(x)h.$$ The derivative of a product is not the product of derivatives: each factor is varied in turn with the other held fixed, which is exactly what makes differentiation a derivation rather than a ring homomorphism. Stating it for the Frechet derivative extends it to maps from any normed space, and to noncommutative targets such as matrices or operators, where the order of the factors in each term genuinely matters. **Formalization note.** The target is a normed algebra over the base field. The result is Mathlib's `fderiv_mul`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem fderiv_mul :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] 
    [inst_2 : NormedSpace 𝕜 E] {x : E} {𝔸' : Type u_3} [inst_3 : NormedCommRing 𝔸'] [inst_4 : NormedAlgebra 𝕜 𝔸'] 
    {c d : E → 𝔸'}, 
    DifferentiableAt 𝕜 c x → DifferentiableAt 𝕜 d x → fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x := by sorry

end FamousTheorems
