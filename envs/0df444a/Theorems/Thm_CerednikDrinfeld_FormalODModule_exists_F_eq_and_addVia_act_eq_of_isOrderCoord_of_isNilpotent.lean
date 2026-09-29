-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/b8352628-9ee3-5646-b6db-729aefc0048a
-- title:
--   Lattice action on a formal group yields a formal mathcal O_D-module
-- statement:
--   Fix rationals $a,b$, a prime $q$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, and a map $\mathrm{coord}\colon\Lambda\to \mathrm{Zp2}\,q\times \mathrm{Zp2}\,q$, where $\mathrm{Zp2}\,q$ is the Witt vectors of the field with $q^2$ elements, assumed to satisfy `IsOrderCoord`: it is additive; it sends $1$ to $(1,0)$ whenever $1\in\Lambda$; for $m,m'\in\Lambda$ with $mm'\in\Lambda$ it obeys the twisted multiplication rule $\mathrm{coord}(mm')=(\alpha\alpha'+q\beta\,\sigma(\beta'),\ \alpha\beta'+\beta\,\sigma(\alpha'))$ with $\sigma$ the Witt-vector Frobenius; it is injective; its image is dense, in the sense that each pair $(\alpha,\beta)$ is matched modulo $q^k$ by some $\mathrm{coord}(m)$; and $\alpha+\sigma(\alpha)=n$ whenever $m+\bar m=n\in\mathbb Z$. Let $B$ be a commutative ring in which the image of $q$ is nilpotent, $F$ a commutative $2$-dimensional formal group law over $B$, and $\rho\colon\Lambda\to\operatorname{End}F$ a map which is additive and satisfies $\rho(mm')=\rho(m)\rho(m')$ whenever $mm'\in\Lambda$, and for which there is an $n$ coprime to $q$ with $n\in\Lambda$, $\mathrm{coord}(n)=(n,0)$ and $\rho(n)$ given by the $n$-th multiplication series of $F$. Then there exists a formal $\mathcal O_D$-module $X$ over $B$ (a commutative $2$-dimensional law with endomorphisms $[\alpha]_X$ for $\alpha\in\mathrm{Zp2}\,q$ and $\varpi_X$, satisfying $[1]_X=\mathrm{id}$, $[\alpha\beta]_X=[\alpha]_X\circ[\beta]_X$, $[\alpha+\beta]_X=[\alpha]_X+_F[\beta]_X$, $\varpi_X\circ\varpi_X=[q]_X$ and $\varpi_X\circ[\alpha]_X=[\sigma(\alpha)]_X\circ\varpi_X$) whose underlying law is exactly $F$ and such that for every $m\in\Lambda$ with $\mathrm{coord}(m)=(\alpha,\beta)$ one has $\rho(m)=[\alpha]_X+_F([\beta]_X\circ\varpi_X)$ as tuples of power series.
--
--   This is the formal-module side of the Čerednik–Drinfeld description of quaternionic uniformisation: an action of a quaternionic lattice with $q$-adically dense coordinates on a two-dimensional formal group over a $q$-nilpotent base is rigidified into an action of the maximal order $\mathcal O_D$ of the ramified quaternion algebra over $\mathbb Q_q$, with its uniformiser $\varpi$. It is used in the construction of the formal module attached to a fake elliptic curve, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.FormalODModule.exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : CerednikDrinfeld.QM.IsOrderCoord Λ q coord)
    (B : Type u) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (F : MvFormalGroup 2 B) [F.IsComm] (ρ : ↥Λ → MvFormalGroup.End F)
    (hadd : ∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m')
    (hmul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m * ρ m')
    (hunit : ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        (ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩).toPowerSeries = F.nthSeries n) :
    ∃ X : FormalODModule q B, X.F = F ∧
      ∀ m : ↥Λ, Series.addVia F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) =
        (ρ m).toPowerSeries := by sorry
