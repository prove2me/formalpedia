-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
-- name    : AlgebraicGeometry.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/b6151dfa-0bb5-538d-9ce8-e9e089d595bb
-- title:
--   Sections over a local ring agreeing at the closed point
-- statement:
--   Let $A$ be a commutative local ring, let $X$ be a scheme, and let $c : X \to \operatorname{Spec} A$ be a morphism of schemes. Let $\sigma, \sigma' : \operatorname{Spec} A \to X$ be two sections of $c$, in the sense that $\sigma$ followed by $c$ and $\sigma'$ followed by $c$ are both the identity of $\operatorname{Spec} A$. Assume the two sections send the closed point of $\operatorname{Spec} A$ to the same point $x$ of $X$, i.e. $\sigma'$ and $\sigma$ agree on underlying spaces at `IsLocalRing.closedPoint A`. Assume further the kernel inclusion, phrased on germs at that point: for every open $U \subseteq X$ containing $x = \sigma(\mathfrak m_A)$ and every section $s \in \mathcal O_X(U)$, if the germ of $s$ at $x$ is annihilated by the stalk map of $\sigma$ at the closed point, then the germ of $s$ at $\sigma'(\mathfrak m_A)$ (the same point, via the assumed equality) is annihilated by the stalk map of $\sigma'$ at the closed point. The conclusion is that $\sigma = \sigma'$ as morphisms of schemes. Thus $\ker(\sigma^\sharp_x) \subseteq \ker(\sigma'^\sharp_x)$ together with equality of the images of the closed point forces the two sections to coincide.
--
--   This is a rigidity statement for sections of a scheme over the spectrum of a local ring: such a section is determined by the image of the closed point together with the kernel of the induced map on the stalk there. It is used in the study of smooth relative curves, where it rules out a second point with the same reduction at which a given function fails to be a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem AlgebraicGeometry.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (σ σ' : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hσ' : σ' ≫ c = 𝟙 _)
    (hx : σ'.base (IsLocalRing.closedPoint A) = σ.base (IsLocalRing.closedPoint A))

    (hker : ∀ (U : X.Opens) (hU : σ.base (IsLocalRing.closedPoint A) ∈ U) (s : X.presheaf.obj (Opposite.op U)),
      (σ.stalkMap (IsLocalRing.closedPoint A)).hom (X.presheaf.germ U (σ.base (IsLocalRing.closedPoint A)) hU s) = 0 →
      (σ'.stalkMap (IsLocalRing.closedPoint A)).hom
        (X.presheaf.germ U (σ'.base (IsLocalRing.closedPoint A)) (by rw [hx]; exact hU) s) = 0) :
    σ = σ' := by sorry
