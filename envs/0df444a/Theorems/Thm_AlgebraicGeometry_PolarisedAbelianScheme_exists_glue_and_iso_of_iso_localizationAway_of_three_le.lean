-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_glue_and_iso_of_iso_localizationAway_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_glue_and_iso_of_iso_localizationAway_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/2c087b7e-d518-57e9-ae52-6f40b37c57a6
-- title:
--   Zariski gluing and separation for polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$, a commutative ring $S$ (in the lowest universe) in which the image of $n$ is a unit, elements $r_0,\dots,r_{k-1} \in S$ whose span is the unit ideal, and for each $i$ an $S$-algebra $B_i$ which is a localisation of $S$ away from $r_i$. Here an object of `PolarisedAbelianScheme g d n S` consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ (a functorial, natural group structure on the sets of $T$-points of $f$ over each $t : T \to \operatorname{Spec} S$) that is commutative, the property bundle asserting $f$ smooth, proper, with connected fibres and admitting a group law, the condition that every fibre of $f$ has topological Krull dimension $g$, a family $P_0,\dots,P_{2g-1}$ of sections of $f$ killed by $n$ such that on every geometric fibre over an algebraically closed field the $n$-fold products of the $P_i$ with exponents in $\mathrm{Fin}\ n$ are pairwise distinct and exhaust the $n$-torsion, together with a module `pol` on $A$ which is invertible (locally trivial of rank one), defines a closed immersion into projective space by its sections, and has geometric fibrewise $H^0$ of dimension $d$. Two such objects over $S$ are isomorphic when there is an isomorphism of the underlying schemes over $\operatorname{Spec} S$ compatible with the group laws, carrying each $P_i$ to $P_i'$, and identifying the two polarising modules locally on the base; an object $u'$ over $S'$ is a base change of $u$ along $\varphi : S \to S'$ when there is a morphism $u'.A \to u.A$ making the square with $\operatorname{Spec} \varphi$ a pullback, compatible with the group laws and the chosen sections, and pulling `pol` back to $u'$'s polarisation. The theorem asserts the conjunction of two statements. First (gluing): for every family $u$ of objects $u_i$ over $B_i$ such that for all $i,j$, every $S$-algebra $C$ which is a localisation away from $r_i r_j$, all $S$-algebra maps $\rho_1 : B_i \to C$, $\rho_2 : B_j \to C$ and all objects $v_1, v_2$ over $C$ which are base changes of $u_i$ along $\rho_1$ and of $u_j$ along $\rho_2$ respectively satisfy $v_1 \cong v_2$, there exists an object $u_0$ over $S$ such that for each $i$ every object $v$ over $B_i$ which is a base change of $u_0$ along $S \to B_i$ satisfies $v \cong u_i$. Second (separation): if $u_0, u_0'$ are objects over $S$ such that for every $i$ any base changes $v$ of $u_0$ and $v'$ of $u_0'$ to $B_i$ satisfy $v \cong v'$, then $u_0 \cong u_0'$. Note that no existence of base changes is asserted; both conclusions are conditional on objects realising them.
--
--   This is the Zariski-sheaf property of the moduli problem of $g$-dimensional polarised abelian schemes of degree $d$ with full level-$n$ structure for $n \ge 3$: descent of objects along a finite Zariski cover $\operatorname{Spec} B_i \to \operatorname{Spec} S$ given agreement on overlaps, together with the separation statement that local isomorphy implies global isomorphy. It feeds the construction of a fine moduli space from its framed local form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_glue_and_iso_of_iso_localizationAway_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_glue_and_iso_of_iso_localizationAway_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)] :
    (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B i)),
      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
          (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
          PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
          PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
          PolarisedAbelianScheme.Iso v₁ v₂) →
      ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k) (v : PolarisedAbelianScheme g d n (B i)),
        PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) ∧
    (∀ (u₀ u₀' : PolarisedAbelianScheme g d n S),
      (∀ (i : Fin k) (v v' : PolarisedAbelianScheme g d n (B i)),
        PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v →
        PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀' v' →
        PolarisedAbelianScheme.Iso v v') →
      PolarisedAbelianScheme.Iso u₀ u₀') := by sorry
