-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/f578a248-1357-5c77-a95f-97d9b67cad4d
-- title:
--   Base change relation: congruence in φ and reflexivity
-- statement:
--   Fix natural numbers $g,d,n$ and commutative rings $S,S'$. Two assertions are made about the relation `PolarisedAbelianScheme.IsPullback`, which for a ring homomorphism $\varphi : S \to S'$ and objects $u$ over $S$, $v$ over $S'$ (each consisting of a scheme over $\mathrm{Spec}$ of the base ring, carrying a commutative relative group law, the smoothness/properness/connected-fibres bundle, fibres of topological Krull dimension $g$, a family of $2g$ sections killed by $n$ that is independent and spanning on geometrically algebraically closed fibres, and an invertible module, closed-immersion-inducing by sections, with geometric fibre $H^0$-rank $d$) asserts the existence of a morphism $g_A : v.A \to u.A$ making the square with the structure morphisms and $\mathrm{Spec}(\varphi)$ cartesian, compatible with multiplication of $T$-valued points for every $T$ over $\mathrm{Spec}(S')$, carrying each marked section $P_i$ of $v$ to $\mathrm{Spec}(\varphi)$ followed by $P_i$ of $u$, and such that the pullback of the polarising module of $u$ along $g_A$ is isomorphic to that of $v$. First: if $\varphi = \psi$ as ring homomorphisms $S \to S'$, then `IsPullback` for $\varphi$ implies `IsPullback` for $\psi$. Second: for every $u$ over $S$, `IsPullback` holds for the identity of $S$ with $u$ on both sides.
--
--   These are the elementary congruence and reflexivity properties of the base-change relation on polarised abelian schemes with marked $n$-torsion sections, the relation used to formulate representability of the corresponding moduli problem. They are cited by the lemmas on fine moduli and on existence of points compatible with transition maps, where equalities of composite ring maps must be transported and where the identity base change must be recognised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] :
    (∀ (φ ψ : S →+* S') (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S'),
      φ = ψ → PolarisedAbelianScheme.IsPullback φ u v → PolarisedAbelianScheme.IsPullback ψ u v) ∧
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.IsPullback (RingHom.id S) u u) := by sorry
