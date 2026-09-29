-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
-- name    : AlgebraicGeometry.finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/70b66437-4d97-5666-b596-093c071d8ac7
-- title:
--   Counting sections meeting a given open of the special fibre
-- statement:
--   Let $R$ be a commutative domain that is a valuation ring and a henselian local ring, with residue field $\kappa =$ `IsLocalRing.ResidueField R`. Let $X, Y$ be schemes and $g : X \to \operatorname{Spec} R$ a morphism that is locally of finite type, locally quasi-finite, separated and quasi-compact. Let $q : Y \to \operatorname{Spec}\kappa$ and $\pi : Y \to X$ be morphisms such that the square formed by $\pi$, $q$, $g$ and $\operatorname{Spec}$ of the residue map $R \to \kappa$ is cartesian, so that $Y$ together with $\pi, q$ realises the special fibre of $g$. Let $V$ be an open subscheme of $Y$ and $B$ a natural number, and equip $\Gamma(Y, V)$ with the $\kappa$-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom q V` coming from the ring map underlying the inverse of the iso $\Gamma(\operatorname{Spec}\kappa,\top)\cong\kappa$ followed by $q$'s restriction map $q.\mathrm{appLE}\ \top\ V$. Assume $\Gamma(Y, V)$ is a finite $\kappa$-module with $\dim_\kappa \Gamma(Y, V) \le B$. Then the set of sections $s : \operatorname{Spec} R \to X$ of $g$ (that is, $s$ followed by $g$ is the identity) whose value at the closed point of $R$ lies in the image $\pi(V) \subseteq X$ is finite, and its cardinality is at most $B$.
--
--   This is the local form, relative to an open $V$ of the special fibre, of the bound on the number of $R$-points of a separated quasi-compact, locally quasi-finite $R$-scheme over a henselian valuation ring (compare EGA IV 18.5.11); the global case $V = \top$ is [`AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le`](thm.html#AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le). It is used in the counting of sections of the Néron model of $J_0$ at $p$ whose reduction lies in a prescribed open of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (V : Y.Opens) (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q V
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, V) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, V) ≤ B) :
    Finite {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ∧
      Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧
        s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ≤ B := by sorry
