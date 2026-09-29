-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective
-- name    : AlgebraicGeometry.Scheme.Modules.epi_sheafification_map_of_locallySurjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a9ec8da1-1a25-5c4f-839e-7c7b22211320
-- title:
--   Sheafification of a locally surjective map of presheaves of modules is epi
-- statement:
--   Let $X$ be a scheme and let $P$ and $Q$ be presheaves of $\mathcal O_X$-modules, that is, objects of `X.PresheafOfModules`, presheaves of modules over the presheaf of rings underlying the structure sheaf of $X$. Let $\psi \colon P \to Q$ be a morphism of such presheaves of modules. Assume that $\psi$ is locally surjective in the sectionwise sense: for every open $U \subseteq X$, every section $s \in Q(U)$ and every point $x \in U$ there exist an open $V$ with $V \le U$ and $x \in V$ such that the restriction $s|_V = Q(V \le U)(s)$ lies in the range of the component $\psi_V \colon P(V) \to Q(V)$, i.e. $s|_V = \psi_V(t)$ for some $t \in P(V)$. Then the image of $\psi$ under the sheafification functor `PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`, which sends a presheaf of modules over the presheaf of rings underlying $X.\mathrm{ringCatSheaf}$ to the associated sheaf of $\mathcal O_X$-modules, is an epimorphism in the category of sheaves of $\mathcal O_X$-modules on $X$.
--
--   This is the standard statement that a sectionwise locally surjective morphism of presheaves of modules becomes a surjection of associated sheaves, phrased for the Grothendieck topology of opens of a scheme. It is the tool by which sheaf-level surjectivity is verified for maps constructed on sections, and is used in the project to show that the morphism obtained by whiskering a short exact sequence's associated wedge-power construction is an epimorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.epi_sheafification_map_of_locallySurjective
    {X : Scheme.{u}} {P Q : X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ψ) := by sorry
