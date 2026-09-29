-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1eea3acd-c518-504f-9c31-9dd5d82924b9
-- title:
--   Zariski gluing of level-n polarised abelian schemes, n ≥ 3
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$, a commutative ring $S$ in which the image of $n$ is a unit, elements $r_0,\dots,r_{k-1}$ of $S$ generating the unit ideal, and for each $i$ a commutative $S$-algebra $B_i$ realised as a localisation of $S$ away from $r_i$. Here a term of `PolarisedAbelianScheme g d n R` consists of a scheme $A$ over $\operatorname{Spec} R$ carrying a commutative relative group law, satisfying the bundle of properties smooth, proper, connected fibres and admitting a group law, with all fibres of topological Krull dimension $g$, together with $2g$ sections $P_i$ killed by $n$ which, on every geometric fibre over an algebraically closed field, are $\mathbb{Z}/n$-independent and span the $n$-torsion, and an invertible module `pol` whose sections define a closed immersion into a projective bundle and whose geometric fibre $H^0$ has dimension $d$ everywhere. The assertion is: for every family $u$ with $u_i$ such an object over $B_i$, if for all $i,j$, every localisation $C$ of $S$ away from $r_ir_j$ with $S$-algebra maps $\rho_1 : B_i \to C$, $\rho_2 : B_j \to C$, and all $v_1, v_2$ over $C$ that are pullbacks of $u_i$ along $\rho_1$ and of $u_j$ along $\rho_2$ respectively, one has $v_1 \cong v_2$, then there exists $u_0$ over $S$ such that for each $i$ every pullback $v$ of $u_0$ along $S \to B_i$ satisfies $v \cong u_i$. Pullback means a cartesian square of total spaces compatible with the group laws and the marked sections and matching the polarisations up to isomorphism; isomorphism means an isomorphism of total spaces over the base respecting multiplication and the marked sections, and matching the polarisations locally on the base.
--
--   This is the existence half of the Zariski-sheaf property for polarised abelian schemes with full level-$n$ structure, $n \ge 3$: objects given on a basic-open cover of $\operatorname{Spec} S$ and agreeing on overlaps descend to the base. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_glue_and_iso_of_iso_localizationAway_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_glue_and_iso_of_iso_localizationAway_of_three_le), whose other half is the corresponding uniqueness (separation) statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le
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
        PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) := by sorry
