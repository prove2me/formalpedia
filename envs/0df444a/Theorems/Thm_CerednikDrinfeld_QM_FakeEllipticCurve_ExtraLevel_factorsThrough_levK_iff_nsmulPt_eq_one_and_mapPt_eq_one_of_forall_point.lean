-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_forall_point
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_forall_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/69ae1638-ef90-5183-9cd4-b34f9fb27ebb
-- title:
--   Extra level at ℓ equals ℓ-torsion killed by f
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, that is, an order (containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$, finitely generated) maximal among orders. Let $N$ be a nonzero natural number, $k_0$ an algebraically closed field, and $E$ a fake elliptic curve over $k_0$ of level $N$ for $\Lambda$, with structure morphism $E.f : E.A \to \operatorname{Spec} k_0$ and relative group law $E.L$. Let $\ell$ be prime with $\ell \neq 0$ in $k_0$, and let $f : E.A \to E.A$ satisfy $E.f \circ f = E.f$ and be a homomorphism for the group law: for every scheme $T$, every $t : T \to \operatorname{Spec} k_0$ and all $T$-points $P,Q$ of $E.f$ over $t$ (i.e. morphisms to $E.A$ composing with $E.f$ to $t$), composition with $f$ takes $E.L.\mathrm{mul}\,t\,P\,Q$ to the product of the images. Let $K$ be an extra level at $\ell$ on $E$, with closed immersion $K.\mathrm{levK}$ into $E.A$, finite flat of finite presentation of fibre rank $\ell^2$, whose points form a $\Lambda$-stable subgroup killed by $\ell$ and meeting the level-$N$ structure trivially, with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$. Finally let $W : \mathbb{Z}/\ell \times \mathbb{Z}/\ell \to$ ($k_0$-points of $E.f$ over $\mathbb{1}_{\operatorname{Spec} k_0}$) be injective, with each $W(i)$ factoring through $K.\mathrm{levK}$ and satisfying $f(W(i)) = E.L.\mathrm{one}$, and such that every $k_0$-point $P$ with $\ell P = E.L.\mathrm{one}$ and $f(P) = E.L.\mathrm{one}$ equals some $W(i)$. Then for every scheme $T$, every $t : T \to \operatorname{Spec} k_0$ and every $T$-point $P$ of $E.f$ over $t$, $P$ factors through $K.\mathrm{levK}$ (there is $P_0 : T \to K.K$ with $P_0$ followed by $K.\mathrm{levK}$ equal to $P$) if and only if $\ell P = E.L.\mathrm{one}\,t$ and $f(P) = E.L.\mathrm{one}\,t$.
--
--   The statement upgrades a description of the $k_0$-rational points of an extra level at $\ell$ to a description of its $T$-points for every base $T$: the subscheme $K$ represents the intersection of the $\ell$-torsion with the kernel of the endomorphism $f$, functorially. It is used in the construction of an extra level whose points are cut out by such an endomorphism, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_forall_point.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_forall_point
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (E : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : (ℓ : k₀) ≠ 0)
    (f : E.A ⟶ E.A) (hf : f ≫ E.f = E.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t E.f),
      mapPt f hf (E.L.mul t P Q) = E.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (K : E.ExtraLevel ℓ)
    (W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) E.f) (hW_inj : Function.Injective W)
    (hW_mem : ∀ i : ZMod ℓ × ZMod ℓ, FactorsThrough K.levK (W i))
    (hW_kill : ∀ i : ZMod ℓ × ZMod ℓ, mapPt f hf (W i) = E.L.one (𝟙 (Spec (CommRingCat.of k₀))))
    (hW_all : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k₀))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        mapPt f hf P = E.L.one (𝟙 (Spec (CommRingCat.of k₀))) → ∃ i : ZMod ℓ × ZMod ℓ, W i = P) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P ↔ (nsmulPt E.L t ℓ P = E.L.one t ∧ mapPt f hf P = E.L.one t) := by sorry
