-- Prove2me | Theorems.Thm_FamousTheorems_gabriel_popescu_full_7a
-- name    : FamousTheorems.gabriel_popescu_full_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:56.667819+00:00
-- url     : https://prove2.me/theorems/19fa1205-3988-4083-bbc0-e3b56aeeb376
-- title:
--   The Gabriel–Popescu theorem (Hom(G,–) is full for a separator G)
-- statement:
--   **The Gabriel–Popescu theorem, fullness part.** Let $C$ be a Grothendieck abelian category and $G$ a separator (generator) of $C$, with endomorphism ring $R=\operatorname{End}(G)$. The functor
--   $$\operatorname{Hom}(G,-):C\to\operatorname{Mod}\text{-}R$$
--   is full: every $R$-module homomorphism $\operatorname{Hom}(G,X)\to\operatorname{Hom}(G,Y)$ is induced by a morphism $X\to Y$.
--
--   Gabriel and Popescu proved in 1964 that $\operatorname{Hom}(G,-)$ is fully faithful and has an exact left adjoint. So every Grothendieck category is a localization of a module category. The theorem transfers results from module categories to categories of sheaves, and it is a key step in the Freyd–Mitchell embedding theorem.
--
--   **Formalization note.** Mathlib's `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full`. `preadditiveCoyonedaObj G` is the functor $X\mapsto\operatorname{Hom}(G,X)$, valued in modules over $\operatorname{End}(G)^{\mathrm{op}}$, that is, right $\operatorname{End}(G)$-modules. Faithfulness of this functor is a direct consequence of $G$ being a separator. The existence of an exact left adjoint is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

theorem gabriel_popescu_full_7a {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{v} C] (G : C) (hG : CategoryTheory.IsSeparator G) :
    (CategoryTheory.preadditiveCoyonedaObj G).Full := by sorry

end FamousTheorems
