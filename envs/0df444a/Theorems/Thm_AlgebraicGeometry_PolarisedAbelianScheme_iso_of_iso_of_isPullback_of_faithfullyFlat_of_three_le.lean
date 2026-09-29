-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/3d6a5ea1-b54f-5c7f-a254-92dde6e550aa
-- title:
--   Faithfully flat descent of isomorphisms of polarised abelian schemes, n≥ 3
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$, a commutative ring $S$ in which the image of $n$ is a unit, and a commutative $S$-algebra $S'$ which is faithfully flat as an $S$-module. Let $u_1, u_2$ be objects of `PolarisedAbelianScheme g d n S` and $v_1, v_2$ objects of `PolarisedAbelianScheme g d n S'`; such an object consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$ carrying a commutative relative group law (a group structure on $T$-points over the base, natural in $T$), the property bundle asserting that $f$ is smooth and proper with connected fibres and admits a group law, all fibres of $f$ of topological Krull dimension $g$, a family of $2g$ sections $P_i$ of $f$ each killed by $n$ for the group law and such that over every algebraically closed field the induced points generate the $n$-torsion of the geometric fibre freely (distinct $\mathbb{Z}/n$-combinations are distinct, and every $n$-torsion point is such a combination), together with a module `pol` on $A$ which is invertible, whose sections define a closed immersion into the associated projective presentation, and whose geometric fibre $H^0$-rank is $d$ at every algebraically closed point. Assume that each $v_j$ is a base change of $u_j$ along $\operatorname{Spec}$ of $\operatorname{algebraMap} S\,S'$ in the sense of `PolarisedAbelianScheme.IsPullback`: there is a morphism $v_j.A \to u_j.A$ forming a pullback square with the structure morphisms and $\operatorname{Spec}(S' ) \to \operatorname{Spec}(S)$, compatible with the group laws on points, matching the marked sections, and identifying the pullback of $u_j.\mathrm{pol}$ with $v_j.\mathrm{pol}$. If $v_1$ and $v_2$ are isomorphic, i.e. there is an isomorphism $v_1.A \cong v_2.A$ over $\operatorname{Spec} S'$ respecting the group laws on points, carrying each marked section to the corresponding one, and with the pullback of $v_2.\mathrm{pol}$ isomorphic to $v_1.\mathrm{pol}$ locally on the base, then $u_1$ and $u_2$ are isomorphic in the same sense over $S$.
--
--   This is the separatedness (descent of isomorphisms) statement for the moduli prestack of polarised abelian schemes with full level-$n$ structure, $n \ge 3$ invertible on the base, along a faithfully flat base change of rings. It is used in the construction of descent data for such objects, being cited by the two `exists_descent_and_iso_of_faithfullyFlat_of_three_le` results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S')
    (h₁ : PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁)
    (h₂ : PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂)
    (h : PolarisedAbelianScheme.Iso v₁ v₂) :
    PolarisedAbelianScheme.Iso u₁ u₂ := by sorry
