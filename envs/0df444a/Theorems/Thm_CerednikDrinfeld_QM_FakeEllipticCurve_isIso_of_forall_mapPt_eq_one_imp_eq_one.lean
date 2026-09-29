-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIso_of_forall_mapPt_eq_one_imp_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isIso_of_forall_mapPt_eq_one_imp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/278868be-08a9-5886-a71a-8c7d9a85719a
-- title:
--   Trivial kernel on k-points forces an isomorphism
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N\in\mathbb{N}$, and let $k$ be an algebraically closed field (in the base universe). Let $E,E'$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, i.e. schemes $E.A$, $E'.A$ with structure morphisms to $\operatorname{Spec} k$, commutative relative group laws on their functors of points, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law exists), two-dimensional fibres, and an action of $\Lambda$ by endomorphisms over the base satisfying the multiplicativity, additivity and trace axioms of the structure. Let $\varphi' : E.A \to E'.A$ be a morphism over $\operatorname{Spec} k$ which is additive on $T$-points for every test scheme $T$ over $\operatorname{Spec} k$ (composition with $\varphi'$ carries $E.L$-multiplication to $E'.L$-multiplication) and which commutes with the $\Lambda$-action, $E.\mathrm{act}(x)$ followed by $\varphi'$ equal to $\varphi'$ followed by $E'.\mathrm{act}(x)$ for every $x\in\Lambda$. Let $\psi' : E'.A \to E.A$ be a morphism over $\operatorname{Spec} k$ and $n' \ge 1$ a natural number whose image in $k$ is nonzero, such that on points over every base-scheme $T$ the composite $\psi'\circ\varphi'$ is the $n'$-fold iterate of the group law of $E$ (defined by $0\mapsto$ unit, $n+1 \mapsto$ multiply the $n$-fold multiple by the point) and $\varphi'\circ\psi'$ is the corresponding $n'$-fold multiple for $E'$. Assume finally that the only $k$-point of $E$ (section of $E.f$ over the identity of $\operatorname{Spec} k$) whose image under $\varphi'$ is the unit section of $E'$ is the unit section of $E$. Then $\varphi'$ is an isomorphism of schemes.
--
--   This is the standard criterion that an isogeny of abelian varieties over an algebraically closed field whose kernel is reduced and has only the trivial rational point is an isomorphism, here in the setting of fake elliptic curves with quaternionic multiplication. It is used in the Čerednik–Drinfeld part of the argument to recognise level isogenies and Hecke neighbours, and to control the annihilator of a non-isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIso_of_forall_mapPt_eq_one_imp_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isIso_of_forall_mapPt_eq_one_imp_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k]
    (E E' : FakeEllipticCurve Λ N k)
    (φ' : E.A ⟶ E'.A) (hφ' : φ' ≫ E'.f = E.f)
    (hφ'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ' hφ' (E.L.mul t P Q) = E'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (hφ'act : ∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E'.act x)
    (ψ' : E'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E'.f)
    (n' : ℕ) (hn' : 0 < n') (hn'k : (n' : k) ≠ 0)
    (hψφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt E.L t n' P)
    (hφψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt E'.L t n' Q)

    (htriv : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      mapPt φ' hφ' P = E'.L.one (𝟙 (Spec (CommRingCat.of k))) → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    IsIso φ' := by sorry
