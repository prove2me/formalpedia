-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_piEvalRingHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7ba9a3c2-b6d0-5302-a9b8-6977cc2383b2
-- title:
--   Triviality over a finite product of rings, factorwise
-- statement:
--   Let $k$ be a natural number and let $R_0,\dots,R_{k-1}$ be commutative rings indexed by $\mathrm{Fin}\,k$, and put $R=\prod_i R_i$. Let $N$ be a sheaf of modules over the structure sheaf of rings of $\operatorname{Spec} R$, i.e. an object of $(\operatorname{Spec} R)\mathord.\mathtt{Modules}$. Suppose that for every index $i$ the pullback of $N$ along the morphism of schemes $\operatorname{Spec}$ of the projection ring homomorphism $\mathrm{Pi.evalRingHom}\ R\ i : R \to R_i$, taken in the sense of `Scheme.Modules.pullback`, admits an isomorphism to the unit object `SheafOfModules.unit` of the category of sheaves of modules over the structure sheaf of $\operatorname{Spec} R_i$ — that is, to the structure sheaf regarded as a module over itself; the hypothesis is stated as nonemptiness of the type of such isomorphisms, for each $i$. The conclusion is that the type of isomorphisms between $N$ and the unit object `SheafOfModules.unit` over $\operatorname{Spec} R$ is nonempty; no compatibility between the given factorwise trivialisations is assumed, and no particular global isomorphism is produced.
--
--   This is the statement that a sheaf of modules on the spectrum of a finite product of rings is trivial as soon as its restriction to each factor is, the factors $\operatorname{Spec} R_i$ forming a finite cover of $\operatorname{Spec} R$ by pairwise disjoint open subschemes on which the gluing cocycle condition is vacuous. It is used in the construction of finite covers by opens over which an invertible sheaf of modules becomes trivial, via [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_finite_away_cover_trivial`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_finite_away_cover_trivial), and relies on the gluing statement [`AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top`](thm.html#AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top) for isomorphisms of sheaves of modules along an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_piEvalRingHom
    {k : ℕ} (R : Fin k → Type u) [∀ i, CommRing (R i)]
    (N : (Spec (CommRingCat.of (∀ i, R i))).Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))).obj N ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R i))).ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit (Spec (CommRingCat.of (∀ i, R i))).ringCatSheaf) := by sorry
