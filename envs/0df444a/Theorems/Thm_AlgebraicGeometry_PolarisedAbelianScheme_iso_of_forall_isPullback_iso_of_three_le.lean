-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_isPullback_iso_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_isPullback_iso_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/14f8628c-7889-5299-b259-bbe8f76d1965
-- title:
--   Zariski-local uniqueness of polarised abelian schemes, n≥ 3
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$, and a commutative ring $S$ in which the image of $n$ is a unit. Let $r : \mathrm{Fin}\,k \to S$ be finitely many elements spanning the unit ideal, and for each $i$ let $B_i$ be a commutative $S$-algebra realised as a localisation of $S$ away from $r_i$. Let $u_0, u_0'$ be two objects of `PolarisedAbelianScheme g d n S`, that is, each consists of a scheme $A$ with a morphism $f$ to $\operatorname{Spec} S$, a commutative relative group law on the functor of points of $f$, an `AbelianSchemePropertyBundle` ($f$ smooth, proper, with connected fibres and admitting a relative group law), all fibres of $f$ of topological Krull dimension $g$, a family of $2g$ sections killed by $n$ whose $\mathrm{Fin}\,n$-combinations are pairwise distinct and exhaust the $n$-torsion over every algebraically closed field point, together with an invertible module `pol` on $A$ which is a closed immersion by sections (a projective presentation over $f$ with closed-immersion morphism to projective space) and has geometric fibre $H^0$-rank $d$. Assume that for every index $i$ and every pair $v, v'$ of polarised abelian schemes of type $(g,d,n)$ over $B_i$ which are pullbacks of $u_0$, respectively $u_0'$, along $S \to B_i$ — pullback meaning a morphism of total spaces making the square with $\operatorname{Spec} B_i \to \operatorname{Spec} S$ cartesian, compatible with the group laws and the $2g$ sections, and identifying the pulled-back polarisation — one has $v \cong v'$ in the sense of `PolarisedAbelianScheme.Iso`. The conclusion is that $u_0$ and $u_0'$ are themselves isomorphic over $S$: an isomorphism of schemes over $\operatorname{Spec} S$ compatible with the group laws and carrying the $2g$ sections of $u_0$ to those of $u_0'$, and locally on the base identifying the two polarisations.
--
--   This is the descent (Zariski-sheaf) half of the uniqueness statement for rigidified polarised abelian schemes with full level-$n$ structure, $n \ge 3$: isomorphisms of such objects are detected on a cover of the base by basic open sets. It is used in the construction of the moduli data, being cited by the gluing and rigidification statements `exists_glue_and_iso_of_iso_localizationAway_of_three_le`, `exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_forall_rigidified` and `QMStructure.iso_of_forall_away_iso`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_isPullback_iso_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_isPullback_iso_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    (u₀ u₀' : PolarisedAbelianScheme g d n S)
    (h : ∀ (i : Fin k) (v v' : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v →
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀' v' →
      PolarisedAbelianScheme.Iso v v') :
    PolarisedAbelianScheme.Iso u₀ u₀' := by sorry
