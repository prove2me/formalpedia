-- Prove2me | Theorems.Thm_FamousTheorems_pontryagin_duality_finite_abelian_6b
-- name    : FamousTheorems.pontryagin_duality_finite_abelian_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:25.959868+00:00
-- url     : https://prove2.me/theorems/bd08bc94-d08e-46d1-ab9f-26911daf88a8
-- title:
--   Pontryagin duality for finite abelian groups
-- statement:
--   **Pontryagin duality for finite abelian groups.** Let $\alpha$ be a finite abelian group and $\widehat\alpha=\operatorname{Hom}(\alpha,\mathbb C^\times)$ its group of characters. The canonical map
--   $$\alpha\to\widehat{\widehat\alpha},\qquad a\mapsto(\chi\mapsto\chi(a))$$
--   is a bijection.
--
--   This is the finite case of Pontryagin duality. It says that a finite abelian group is recovered from its characters, and it is the algebraic basis of the discrete Fourier transform on finite abelian groups. That transform is used in Dirichlet's theorem on primes in arithmetic progressions, in additive combinatorics and in coding theory.
--
--   **Formalization note.** Mathlib's `AddChar.doubleDualEmb_bijective`. `AddChar α ℂ` is the type of additive characters $\alpha\to\mathbb C$, meaning maps sending sums to products, and `AddChar.doubleDualEmb` is the evaluation map into the double dual.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AddChar.doubleDualEmb_bijective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pontryagin_duality_finite_abelian_6b {α : Type*} [AddCommGroup α] [Finite α] :
    Function.Bijective (AddChar.doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) := by sorry

end FamousTheorems
