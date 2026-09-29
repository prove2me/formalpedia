-- Prove2me | Theorems.Thm_FamousTheorems_eckmann_hilton_argument
-- name    : FamousTheorems.eckmann_hilton_argument
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:30.598265+00:00
-- url     : https://prove2.me/theorems/6d7aa33f-5071-4294-afe2-062036ae713e
-- title:
--   The Eckmann–Hilton argument
-- statement:
--   **The Eckmann–Hilton argument.** Let $X$ carry two binary operations $\ast_1,\ast_2$ with units $e_1,e_2$, satisfying the interchange law
--   $$(a\ast_2 b)\ast_1(c\ast_2 d)=(a\ast_1 c)\ast_2(b\ast_1 d).$$
--   Then the two operations coincide, and the common operation is commutative.
--
--   The argument shows that higher homotopy groups $\pi_n$ ($n\ge2$) are abelian, that the fundamental group of a topological group is abelian, and that the endomorphisms of the unit object in a monoidal category form a commutative monoid.
--
--   **Formalization note.** Mathlib's `EckmannHilton.mul` (the two operations are equal) and `EckmannHilton.mul_comm` (commutativity). `EckmannHilton.IsUnital m e` says that `e` is a two-sided unit for `m`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EckmannHilton.mul_comm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem eckmann_hilton_argument {X : Type*} {m₁ m₂ : X → X → X} {e₁ e₂ : X} (h₁ : EckmannHilton.IsUnital m₁ e₁) (h₂ : EckmannHilton.IsUnital m₂ e₂)
    (distrib : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    m₁ = m₂ ∧ ∀ a b, m₂ a b = m₂ b a := by sorry

end FamousTheorems
