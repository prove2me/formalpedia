-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/cffe26be-06e2-5f6a-a886-f822b90360d3
-- title:
--   Fake elliptic curves glue along B'×_B B''
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and let $B,B',B''$ be commutative local Artinian rings. Let $\varphi' : B' \to B$ and $\varphi'' : B'' \to B$ be ring homomorphisms that are surjective and whose kernels are nilpotent ideals. Let $E'$, $E''$, $E_B$ be fake elliptic curves of level $1$ for $\Lambda$ over $B'$, $B''$, $B$ respectively, that is, schemes $A$ over $\mathrm{Spec}$ of the base with a commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative, is compatible with the group law, and satisfies the trace condition on tangent spaces over algebraically closed fields, together with the level datum $\mathrm{lev} : C \to A$. Assume given $h' : E_B.A \to E'.A$ and $h'' : E_B.A \to E''.A$ exhibiting $E_B$ as the pull-back of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the sense of `IsPullbackVia`: the square formed by $h'$, the two structure morphisms and $\mathrm{Spec}$ of the homomorphism is cartesian, composition with $h'$ (resp. $h''$) carries the group law on $T$-points to the group law of $E'$ (resp. $E''$) over the composed base point, commutes with the $\Lambda$-actions, and sends $T$-points factoring through the level datum of $E_B$ to points factoring through that of $E'$ (resp. $E''$). The conclusion asserts the existence of a fake elliptic curve $E$ of level $1$ for $\Lambda$ over the ring $\mathrm{pullbackRing}\,\varphi'\,\varphi''$, the subring of $B' \times B''$ of pairs with equal images in $B$, together with morphisms $k' : E'.A \to E.A$ and $k'' : E''.A \to E.A$ exhibiting $E'$ and $E''$ as the pull-backs of $E$ along the two projections `pullbackFst` and `pullbackSnd`, again in the sense of `IsPullbackVia`, such that $k' \circ h' = k'' \circ h''$ and the square $(h',h'',k',k'')$ is a push-out of schemes.
--
--   This is the effectivity (gluing) step for the deformation functor of fake elliptic curves with $\Lambda$-action at level $1$: data over $B'$ and $B''$ agreeing over $B$ descend to data over the fibre product ring, with total space the push-out of the total spaces, in the style of Schlessinger's conditions on functors of Artin rings. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    (E' : FakeEllipticCurve Λ 1 B') (E'' : FakeEllipticCurve Λ 1 B'') (EB : FakeEllipticCurve Λ 1 B)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'') :
    ∃ (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ''))
      (k' : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
      (k'' : E''.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k''),
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' := by sorry
