-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_eq_of_nonempty_iso
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_eq_of_nonempty_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/04597aea-bf4b-5180-8f2a-b9deb75dca44
-- title:
--   Renormalising an isomorphism along a section of a rigidified module
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme, let $f : A \to \operatorname{Spec} S$ be a morphism of schemes and let $e : \operatorname{Spec} S \to A$ be a section of $f$, i.e. $e$ followed by $f$ is the identity of $\operatorname{Spec} S$. Let $N_1$ and $N_2$ be objects of `A.Modules`, the category of sheaves of modules over the sheaf of rings of $A$, and write $e^{*}$ for the pullback functor `Scheme.Modules.pullback e` along $e$. Assume that the type of isomorphisms $e^{*}N_2 \cong \mathcal{O}_{\operatorname{Spec} S}$, where $\mathcal{O}_{\operatorname{Spec} S}$ denotes the unit sheaf of modules `SheafOfModules.unit` of the ring sheaf of $\operatorname{Spec} S$, is nonempty; that is, $e^{*}N_2$ is trivial in the sense of the rigidification condition. Assume further that some isomorphism $\varphi_0 : N_1 \cong N_2$ exists, and let $\nu : e^{*}N_1 \cong e^{*}N_2$ be an arbitrary isomorphism. Then there is an isomorphism $\psi : N_1 \cong N_2$ whose pullback $e^{*}\psi$ has underlying morphism equal to that of $\nu$.
--
--   This is the normalisation step in the theory of line bundles rigidified along a section: once a module is trivialised along $e$, any prescribed isomorphism on the fibre at $e$ can be realised by globally adjusting a given isomorphism. It is used in the construction of descent data for the relative Picard functor, where an isomorphism of pullbacks must first be normalised along the diagonal section before the cocycle condition is verified, as in [`AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_eq_of_nonempty_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_eq_of_nonempty_iso
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (N₁ N₂ : A.Modules)
    (hN₂ : Nonempty ((Scheme.Modules.pullback e).obj N₂ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (φ₀ : N₁ ≅ N₂) (ν : (Scheme.Modules.pullback e).obj N₁ ≅ (Scheme.Modules.pullback e).obj N₂) :
    ∃ ψ : N₁ ≅ N₂, (Scheme.Modules.pullback e).map ψ.hom = ν.hom := by sorry
