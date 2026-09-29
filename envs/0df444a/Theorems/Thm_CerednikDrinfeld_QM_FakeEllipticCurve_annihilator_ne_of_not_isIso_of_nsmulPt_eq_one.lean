-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_annihilator_ne_of_not_isIso_of_nsmulPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.annihilator_ne_of_not_isIso_of_nsmulPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/365c3b65-e4ad-556c-a3c5-012718817633
-- title:
--   Kernel ideal of a non-isomorphic Hecke isogeny is neither rΛ nor Λ
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and an algebraically closed field $k$. Let $E,E'$ be fake elliptic curves over $k$ for the data $(\Lambda,N)$, i.e. schemes $E.A$, $E'.A$ proper and smooth over $\operatorname{Spec} k$ with connected fibres of dimension $2$, each carrying a commutative relative group law on its functor of points and an action `act` of $\Lambda$ by endomorphisms over the base compatible with the group law and with multiplication in $\Lambda$. Let $r$ be a natural number invertible in $k$, and let $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ be morphisms over $\operatorname{Spec} k$ which, on $T$-points for every scheme $T$ over $\operatorname{Spec} k$, are homomorphisms for the group laws, commute with the $\Lambda$-actions, and satisfy $\psi\circ\varphi = r\cdot\mathrm{id}$ and $\varphi\circ\psi = r\cdot\mathrm{id}$ (the $r$-fold sum `nsmulPt`, defined by $0\cdot P$ = unit and $(n+1)\cdot P = n\cdot P + P$); assume neither $\varphi$ nor $\psi$ is an isomorphism. Let $P_0$ be a $k$-point of $E.A$ (a section of $E.f$ over the identity of $\operatorname{Spec} k$) with $r\cdot P_0$ the unit point, and assume every $k$-point $P$ of $E.A$ with $r\cdot P$ the unit is of the form $\mathrm{act}(m)\circ P_0$ for some $m\in\Lambda$. Let $J$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ whose elements are exactly those $x\in\Lambda$ with $\varphi\circ \mathrm{act}(x)\circ P_0$ the unit $k$-point of $E'.A$. The conclusion is that $J$ does not coincide with the set of $r$-multiples of elements of $\Lambda$, and that $J \neq \Lambda$.
--
--   This is the step showing that the annihilator ideal attached to the kernel of a degree-$r$ Hecke correspondence between fake elliptic curves is a proper left ideal of $\Lambda$ strictly larger than $r\Lambda$: equality with $r\Lambda$ would force $\varphi$ to be an isomorphism, equality with $\Lambda$ would force $\psi$ to be one. It is used, together with the classification of left ideals of $\Lambda/r\Lambda$, in [`CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified) to identify the kernel of a Hecke neighbour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_annihilator_ne_of_not_isIso_of_nsmulPt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld
open CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.annihilator_ne_of_not_isIso_of_nsmulPt_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k]
    (E E' : FakeEllipticCurve Λ N k) (r : ℕ) (hrk : (r : k) ≠ 0)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x)
    (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (hψmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψact : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t r P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t r Q)
    (hφniso : ¬ IsIso φ) (hψniso : ¬ IsIso ψ)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP₀ : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) r P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))))
    (hgen : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) r P = E.L.one (𝟙 (Spec (CommRingCat.of k))) →
        ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀)
    (J : Submodule ℤ ℍ[ℚ, a, b])
    (hJ : ∀ x, x ∈ J ↔ ∃ hx : x ∈ Λ,
      mapPt φ hφ (pushPt (E.act ⟨x, hx⟩) (E.act_over _) P₀) = E'.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    (¬ ∀ x, x ∈ J ↔ ∃ y ∈ Λ, x = (r : ℤ) • y) ∧ J ≠ Λ := by sorry
