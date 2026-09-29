-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_comp_hom_eq_of_isPullbackVia_fstHom_of_three_le
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.comp_hom_eq_of_isPullbackVia_fstHom_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7d2d3935-73c8-5d5d-9339-b4a0c1593ebc
-- title:
--   Isomorphisms over k[ε] are compatible with the comparison maps
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0<a$ or $0<b$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order containing no strictly larger order), let $N$ be a natural number and $m\geq 3$, and let $k$ be a field in which $m$ is invertible. Let $u$ be a fake elliptic curve for $(\Lambda,N)$ over $k$ together with a full level-$m$ structure, and let $w,t$ be two such objects over the dual numbers $\mathrm{DualNumber}\ k=k[\varepsilon]$. Let $gw:u_1.A\to w_1.A$ and $gt:u_1.A\to t_1.A$ satisfy `FakeEllipticCurve.IsPullbackVia` for the ring map $k[\varepsilon]\to k$ given by $\varepsilon\mapsto 0$: each square over $\operatorname{Spec}$ of that map is cartesian, each morphism transports the relative group law (products of points over a base map into the corresponding products after base change), commutes with the $\Lambda$-actions, and carries points factoring through the level scheme to points factoring through the level scheme downstairs; assume moreover $P_u$ followed by $gw$ (respectively $gt$) equals $\operatorname{Spec}$ of $\varepsilon\mapsto 0$ followed by $P_w$ (respectively $P_t$), where $P_\bullet$ denotes the distinguished point of the level structure. Let $e:w_1.A\cong t_1.A$ be an isomorphism with $e$ followed by $t_1.f$ equal to $w_1.f$, such that pushing points forward along $e$ takes products for the group law of $w_1$ to products for that of $t_1$, such that $w_1.\mathrm{act}\,x$ followed by $e$ equals $e$ followed by $t_1.\mathrm{act}\,x$ for all $x\in\Lambda$, such that a point factors through the level scheme of $w_1$ if and only if its push-forward along $e$ factors through that of $t_1$, and such that the push-forward of $P_w$ along $e$ is $P_t$. Then $gw$ followed by $e$ equals $gt$.
--
--   This is the rigidity statement which makes an abstract isomorphism between two objects over $k[\varepsilon]$ reducing to a fixed $u$ automatically an isomorphism of deformations of $u$, so that isomorphism classes of such objects compute the tangent space of the deformation problem. It is used in the construction of the tangent-space structure on first-order deformations of fake elliptic curves with full level $m$ at points of the Shimura curve moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_comp_hom_eq_of_isPullbackVia_fstHom_of_three_le.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.comp_hom_eq_of_isPullbackVia_fstHom_of_three_le
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} {m : ℕ} (hm : 3 ≤ m)
    (k : Type) [Field k] (hmk : IsUnit ((m : ℕ) : k))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (w t : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k))

    (gw : u.1.A ⟶ w.1.A) (hgw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w.1 u.1 gw)
    (hgwP : (u.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.2.P).1)
    (gt : u.1.A ⟶ t.1.A) (hgt : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t.1 u.1 gt)
    (hgtP : (u.2.P).1 ≫ gt = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t.2.P).1)

    (e : w.1.A ≅ t.1.A) (he : e.hom ≫ t.1.f = w.1.f)
    (hmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver s w.1.f),
      mapPt e.hom he (w.1.L.mul s P Q) = t.1.L.mul s (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, w.1.act x ≫ e.hom = e.hom ≫ t.1.act x)
    (hlev : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver s w.1.f),
      FactorsThrough w.1.lev P ↔ FactorsThrough t.1.lev (mapPt e.hom he P))
    (hP : mapPt e.hom he w.2.P = t.2.P) :
    gw ≫ e.hom = gt := by sorry
