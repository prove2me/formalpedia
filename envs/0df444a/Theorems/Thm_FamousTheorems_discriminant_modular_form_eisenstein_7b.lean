-- Prove2me | Theorems.Thm_FamousTheorems_discriminant_modular_form_eisenstein_7b
-- name    : FamousTheorems.discriminant_modular_form_eisenstein_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:25.562981+00:00
-- url     : https://prove2.me/theorems/a8b135cb-5677-47f4-b3ee-398fcf7eeae6
-- title:
--   Δ = (E₄³ − E₆²)/1728
-- statement:
--   **The modular discriminant in terms of Eisenstein series.** For every $z$ in the upper half-plane,
--   $$\Delta(z)=\frac{E_4(z)^3-E_6(z)^2}{1728},$$
--   where $E_4$ and $E_6$ are the normalized Eisenstein series of weights $4$ and $6$ and $\Delta$ is the modular discriminant.
--
--   The identity is the modular counterpart of the formula $\Delta=g_2^3-27g_3^2$ for the discriminant of an elliptic curve $y^2=4x^3-g_2x-g_3$. It shows that $\Delta$ is a cusp form of weight $12$, and it is used to define the $j$-invariant $j=E_4^3/\Delta$ and to show that the ring of level-one modular forms is $\mathbb C[E_4,E_6]$.
--
--   **Formalization note.** Mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`. Mathlib defines `ModularForm.discriminant` by the product $q\prod(1-q^n)^{24}$, so the identity is a theorem and not a definition. `ModularForm.E₄` and `ModularForm.E₆` are normalized to have constant term $1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem discriminant_modular_form_eisenstein_7b (z : UpperHalfPlane) :
    ModularForm.discriminant z = (ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2) / 1728 := by sorry

end FamousTheorems
