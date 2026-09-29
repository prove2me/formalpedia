-- Prove2me | Theorems.Thm_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
-- name    : AlgebraicGeometry.finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fc79b314-861d-501a-8eb1-46bf9ca6db89
-- title:
--   Global sections of the special fibre compute the finite part
-- statement:
--   Let $R$ be a commutative local ring with residue field $\kappa =$ `IsLocalRing.ResidueField R`, and let $X, X^f, X', Y$ be schemes (all in one universe). Given a morphism $g : X \to \operatorname{Spec} R$, an open immersion $i : X^f \to X$ whose composite $i$ followed by $g$ is a finite morphism, and an arbitrary morphism $j : X' \to X$, assume that the set-theoretic images of $i$ and $j$ cover $X$ (their union is all of the underlying space) and that the closed point of $\operatorname{Spec} R$ does not lie in the image of $j$ followed by $g$. Assume further that $q : Y \to \operatorname{Spec} \kappa$ and $\pi : Y \to X$ form a cartesian square with $g$ and $\operatorname{Spec}$ of the residue map $R \to \kappa$, so that $Y$ is a special fibre $X \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa$. Equip $\Gamma(Y, \mathcal{O}_Y)$ with the $\kappa$-algebra structure coming from the ring map $\kappa \cong \Gamma(\operatorname{Spec}\kappa, \mathcal{O}) \to \Gamma(Y, \mathcal{O}_Y)$ induced by $q$ on global sections, and $\Gamma(X^f, \mathcal{O})$ with the $R$-algebra structure induced in the same way by $i$ followed by $g$. Then $\Gamma(Y, \mathcal{O}_Y)$ is a finite $\kappa$-module, and $\dim_\kappa \Gamma(Y, \mathcal{O}_Y) = \dim_\kappa \bigl(\kappa \otimes_R \Gamma(X^f, \mathcal{O})\bigr)$.
--
--   This is the global-sections form of the statement that, over a local base, a scheme whose complement of a finite open part has empty special fibre has the same special fibre as that finite part; the hypotheses $(i, j, \text{cover}, \text{empty})$ are those produced by the decomposition of a quasi-finite separated scheme into a finite part and a part missing the closed fibre. It feeds the rank and cardinality estimates [`AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le`](thm.html#AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le) and [`AlgebraicGeometry.natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced`](thm.html#AlgebraicGeometry.natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced), and through these the counting of kernel cosets on the Néron model of $J_0$ at $p$ in [`ModularCurve.JZeroNeronObjectAtP.finite_and_card_le_of_kernel_coset_representatives`](thm.html#ModularCurve.JZeroNeronObjectAtP.finite_and_card_le_of_kernel_coset_representatives).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [IsFinite (i ≫ g)] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    letI : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
    Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
    Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) =
      Module.finrank (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R) Γ(Xf, ⊤)) := by sorry
