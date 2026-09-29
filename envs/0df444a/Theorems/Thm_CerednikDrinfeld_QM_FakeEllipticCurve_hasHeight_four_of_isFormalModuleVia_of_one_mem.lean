-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasHeight_four_of_isFormalModuleVia_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hasHeight_four_of_isFormalModuleVia_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/df5838b7-fcce-5cf2-af45-709db73c3493
-- title:
--   Formal mathcal O_D-module of a fake elliptic curve has height four
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$ and a prime $q$. Let $\mathrm{coord}\colon\Lambda\to W(\mathbb F_{q^2})\times W(\mathbb F_{q^2})$ satisfy `IsOrderCoord`: it is additive and injective, sends $1$ (when $1\in\Lambda$) to $(1,0)$, carries products of elements of $\Lambda$ to $(\alpha\alpha'+q\,\beta\,\varphi(\beta'),\ \alpha\beta'+\beta\,\varphi(\alpha'))$ where $\varphi$ is the Witt-vector Frobenius, has image dense for the $q$-adic topology in both coordinates, and satisfies $\alpha+\varphi(\alpha)=n$ whenever $m+\bar m=n\in\mathbb Z$. Assume $1\in\Lambda$. Let $B$ be a Noetherian commutative ring in which the image of $q$ is nilpotent, $E$ a fake elliptic curve over $B$ for $(\Lambda,N)$ — a scheme $A\to\operatorname{Spec}B$ with a commutative relative group law $E.L$, abelian-scheme property bundle, all fibres of dimension $2$, together with an action of $\Lambda$ by endomorphisms over $B$ that is additive, multiplicative and unital and has the prescribed trace on tangent spaces — and let $X$ be a formal $\mathcal O_D$-module over $B$ for $q$: a commutative $2$-dimensional formal group $X.F$ with an action of $W(\mathbb F_{q^2})$ by series endomorphisms and a series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[\alpha]=[\varphi(\alpha)]\circ\varpi$. Suppose $\theta$, a system of formal coordinates of rank $2$ for $E.f$, exhibits $E$ as a formal module via $\mathrm{coord}$, $X$ and $\theta$: $\theta$ is a system of formal coordinates for $E.L$ with formal group $X.F$ (compatible with base change, bijecting nilpotent $2$-tuples with infinitesimal points and matching the group laws), and for every $m\in\Lambda$ the endomorphism $E.\mathrm{act}\ m$ is computed in coordinates by the series $X.F$-sum of $[(\mathrm{coord}\ m)_1]$ and $[(\mathrm{coord}\ m)_2]\circ\varpi$. Then $X$ has height $4$, that is, multiplication by $q$ on $X$ has kernel of degree $q^4$.
--
--   This is the height computation in Drinfeld's theory: at a prime ramified in the quaternion algebra, the formal module attached to a fake elliptic curve over a base in which $q$ is nilpotent is a special formal $\mathcal O_D$-module of height $4$, the $q^4$ coming from the degree of $A[q]$ for an abelian scheme of relative dimension $2$. It feeds the rigidification step of the Čerednik–Drinfeld uniformisation, where the formal module must be known to be of height $4$ before it can be matched with the universal special formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasHeight_four_of_isFormalModuleVia_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hasHeight_four_of_isFormalModuleVia_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (B : Type) [CommRing B] [IsNoetherianRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ) :
    X.HasHeight 4 := by sorry
