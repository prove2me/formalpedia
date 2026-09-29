-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one_of_hom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/66ac1efd-e54f-5004-aa43-5b92f552c8cf
-- title:
--   Factoring a homomorphism killing q-torsion through [q]
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ such that every integer, viewed as a rational scalar in $\mathbb{H}[\mathbb{Q},a,b]$, lies in $\Lambda$; fix a natural number $N$ and a field $k$. Let $E$ and $E'$ be objects of type `FakeEllipticCurve Λ N k`, i.e. schemes $E.A$, $E'.A$ equipped with structure morphisms to $\mathrm{Spec}\,k$, relative commutative group laws $E.L$, $E'.L$ on their functors of points over $\mathrm{Spec}\,k$, smoothness, properness and connectedness of fibres, fibres of topological Krull dimension $2$, actions of $\Lambda$ by endomorphisms over $\mathrm{Spec}\,k$ which are additive on points, compatible with multiplication, addition and the unit of $\Lambda$, satisfy a trace condition, together with the remaining data of that structure. Let $q$ be a natural number with $q \neq 0$ in $k$, and let $\varphi : E.A \to E'.A$ satisfy $\varphi$ followed by $E'.f$ equals $E.f$, be a homomorphism for the group laws on $T$-points (i.e. $P \mapsto P \circ \varphi$ carries $E.L$-products to $E'.L$-products for every $t : T \to \mathrm{Spec}\,k$), commute with the $\Lambda$-actions in the sense that $E.\mathrm{act}\,m$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}\,m$ for all $m \in \Lambda$, and kill $q$-torsion: whenever the $q$-fold iterate of the group law on a point $P$ over $t$ equals the identity section, $P \circ \varphi$ is the identity section of $E'$. The conclusion asserts the existence of $\psi : E.A \to E'.A$ over $\mathrm{Spec}\,k$ which is again a homomorphism on points and commutes with the $\Lambda$-actions, and which satisfies $\varphi = (E.\mathrm{act}\,q)$ followed by $\psi$, where $q$ is taken as the integer scalar $q \in \Lambda$.
--
--   This is the divisibility statement for isogenies of abelian schemes — a homomorphism vanishing on the $q$-torsion factors through multiplication by $q$ — in the two-object form for fake elliptic curves with quaternionic multiplication, and with the factor inheriting additivity and $\Lambda$-equivariance. It is used in the construction of level-$q$ isogenies and of Atkin–Lehner quotient data, where an endomorphism is divided by a quaternionic multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one_of_hom.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_eq_act_comp_of_forall_nsmulPt_eq_one_imp_mapPt_eq_one_of_hom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ}
    (k : Type) [Field k] (E E' : FakeEllipticCurve Λ N k) (q : ℕ) (hq : (q : k) ≠ 0)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_lin : ∀ m : ↥Λ, E.act m ≫ φ = φ ≫ E'.act m)
    (hφ_kill : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      nsmulPt E.L t q P = E.L.one t → mapPt φ hφ P = E'.L.one t) :
    ∃ (ψ : E.A ⟶ E'.A) (hψ : ψ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt ψ hψ (E.L.mul t P Q) = E'.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ m : ↥Λ, E.act m ≫ ψ = ψ ≫ E'.act m) ∧
      φ = E.act ⟨((q : ℤ) : ℚ), hΛℤ q⟩ ≫ ψ := by sorry
