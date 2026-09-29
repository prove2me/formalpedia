-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
-- name    : AlgebraicGeometry.Smooth.exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/4f9f7843-d8ae-5384-b200-0ee79352ab97
-- title:
--   Hensel lifting of residue points of a smooth R-scheme
-- statement:
--   Let $R$ and $A$ be commutative rings in a fixed universe, with $A$ a Henselian local ring and equipped with an $R$-algebra structure, and write $\kappa = \mathrm{IsLocalRing.ResidueField}\,A$. Let $X$ be a scheme and $c \colon X \to \operatorname{Spec} R$ a morphism that is smooth, and let $xk \colon \operatorname{Spec} \kappa \to X$ be a morphism such that $xk$ followed by $c$ equals $\operatorname{Spec}$ of the composite ring map $R \to A \to \kappa$. Then there exists $\sigma \colon \operatorname{Spec} A \to X$ such that: (i) $\sigma$ followed by $c$ is $\operatorname{Spec}$ of the structure map $R \to A$; (ii) $\operatorname{Spec}$ of the residue map $A \to \kappa$ followed by $\sigma$ is $xk$, so that $\sigma$ reduces to the given $\kappa$-point; and (iii) the induced ring map $\mathcal{O}_{X,\sigma(\mathfrak{m}_A)} \to A$ on the stalk at the image of the closed point of $A$ (`Scheme.stalkClosedPointTo`) is $R$-semilinear in the following sense: for every $r \in R$ and every germ $g$ in that stalk, the image of $\gamma_r \cdot g$ equals $(\text{algebraMap }R\,A)(r)$ times the image of $g$, where $\gamma_r$ is the germ at $\sigma(\mathfrak{m}_A)$ of the global section $c^{\#}$ applied to the image of $r$ under the inverse of the Gamma–Spec adjunction isomorphism for $R$.
--
--   This is Hensel's lemma for smooth morphisms over a Henselian local base: $\kappa$-points of a smooth $R$-scheme lift to $A$-points, with the additional statement that evaluation of germs at the lift carries sections pulled back from the base to their images in $A$. It is used in the construction of points of integral models of modular curves over valuation subrings, where lifts of points of a special fibre are required together with control of the values of functions coming from the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
    {R A : Type u} [CommRing R] [CommRing A] [HenselianLocalRing A] [Algebra R A]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [Smooth c]
    (xk : Spec (.of (IsLocalRing.ResidueField A)) ⟶ X)
    (hxk : xk ≫ c = Spec.map (CommRingCat.ofHom ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A)))) :
    ∃ σ : Spec (.of A) ⟶ X,
      σ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) ≫ σ = xk ∧
      ∀ (r : R) (g : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A))),
        (Scheme.stalkClosedPointTo σ).hom
            ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint A)) trivial).hom
              (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) * g) =
          algebraMap R A r * (Scheme.stalkClosedPointTo σ).hom g := by sorry
