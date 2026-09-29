-- Prove2me | Theorems.Thm_FamousTheorems_yoneda_lemma_6b
-- name    : FamousTheorems.yoneda_lemma_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:43.383528+00:00
-- url     : https://prove2.me/theorems/f7a68fab-40eb-4be0-a2c4-dcde20b71822
-- title:
--   The Yoneda lemma
-- statement:
--   **The Yoneda lemma.** Let $\mathcal C$ be a category, $X$ an object of $\mathcal C$ and $F:\mathcal C^{\mathrm{op}}\to\mathbf{Set}$ a presheaf. Natural transformations from the representable presheaf $\operatorname{Hom}(-,X)$ to $F$ correspond bijectively to elements of $F(X)$:
--   $$\operatorname{Nat}\big(\operatorname{Hom}(-,X),F\big)\cong F(X).$$
--
--   The bijection sends $\eta$ to $\eta_X(\mathrm{id}_X)$. The Yoneda lemma is the fundamental result of category theory. It shows that an object is determined up to isomorphism by the morphisms into it, and it is the basis of representable functors, universal properties and the functor-of-points approach to algebraic geometry.
--
--   **Formalization note.** Mathlib's `CategoryTheory.yonedaEquiv`, which is a definition. The statement asserts that such a bijection exists, as a `Nonempty` of the equivalence type. `yoneda.obj X` is the presheaf $\operatorname{Hom}(-,X)$ and `op X` is $X$ viewed in $\mathcal C^{\mathrm{op}}$. The explicit bijection $\eta\mapsto\eta_X(\mathrm{id}_X)$ is part of the definition of `yonedaEquiv` and is not recorded in this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.yonedaEquiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open CategoryTheory Opposite

theorem yoneda_lemma_6b {C : Type*} [Category C] (X : C) (F : Cᵒᵖ ⥤ Type _) :
    Nonempty ((yoneda.obj X ⟶ F) ≃ F.obj (op X)) := by sorry

end FamousTheorems
