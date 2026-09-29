-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/198cbfaa-c0a9-5dd5-a653-637dad0a366f
-- title:
--   Extra level of a pullback pair is a full preimage
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $S,S'$, a ring homomorphism $\varphi : S \to S'$ and a natural number $\ell$. Let $u = (E,K)$ and $u' = (E',K')$ be pairs consisting of a fake elliptic curve with $\Lambda$-action of conductor datum $(\Lambda,N)$ over $S$ resp. $S'$ together with an `ExtraLevel` structure at $\ell$, so that $K \to E.A$ and $K' \to E'.A$ are closed immersions which are finite, flat and locally of finite presentation over the base with fibre rank $\ell^2$. Let $g : E'.A \to E.A$ be a morphism making the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ cartesian, and assume that for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and every $T$-point $P$ of $E'.A$ over $t'$, if $P$ factors through $K' \to E'.A$ then $P$ followed by $g$ factors through $K \to E.A$. Then the converse implication holds: whenever $P$ followed by $g$ factors through $K \to E.A$, $P$ factors through $K' \to E'.A$.
--
--   Together with the hypothesis assumed, this yields that the extra level subscheme $K'$ of a pullback pair is exactly the preimage $g^{-1}(K) = K \times_S S'$ on points valued in arbitrary schemes, the extra-level analogue of the corresponding statement for the level-$N$ structure. It is used in the comparison of extra level structures over algebraically closed fields, in the rigidity statement for pairs sitting in two cartesian squares, and in the construction of morphisms out of objects with full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {ℓ : ℕ}
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_levK : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) :
    ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      (∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) → FactorsThrough u'.2.levK P := by sorry
