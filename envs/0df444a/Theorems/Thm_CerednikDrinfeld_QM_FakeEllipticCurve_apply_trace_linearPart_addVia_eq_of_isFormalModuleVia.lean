-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/31ed0bc2-4fe0-5316-9114-d6385e764ec9
-- title:
--   Drinfeld trace condition for the formal module of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$, and let $\mathrm{coord} : \Lambda \to \mathbb{Z}_{q^2} \times \mathbb{Z}_{q^2}$ be any map into the square of $W(\mathbb{F}_{q^2})$ (`Zp2 q`). Let $B$ be a commutative ring, $E$ a `FakeEllipticCurve Λ N B` with structure morphism $E.f$ and $\Lambda$-action $E.\mathrm{act}$, let $X$ be a formal $\mathcal{O}_D$-module over $B$ of height data $q$ (a two-dimensional commutative formal group law $X.F$ together with series $X.\mathrm{act}$ and $X.\varpi$ satisfying the $\mathcal{O}_D$-relations), and let $\theta$ be a system of formal coordinates of dimension $2$ along $E.f$, assigning to each $B$-algebra $B'$ and each $s : \mathrm{Fin}\,2 \to B'$ a point of $E$ over $\operatorname{Spec} B'$. Assume `E.IsFormalModuleVia coord X θ`: namely that $\theta$ exhibits the group law $E.L$ as $X.F$, and that for every $B$-algebra $B'$, every ideal $J$ with $J^{n+1}=0$, every $m \in \Lambda$ and every $s$ with entries in $J$, the value of $\theta$ at the truncated evaluation at $s$ of the pair of series $S_m := X.\mathrm{act}((\mathrm{coord}\,m)_1) +_{X.F} \bigl(X.\mathrm{act}((\mathrm{coord}\,m)_2) \circ X.\varpi\bigr)$ equals the image of $\theta(s)$ under $E.\mathrm{act}\,m$. Let $k$ be an algebraically closed field, $sk : B \to k$ a ring homomorphism, $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m + \bar m = n$ in $\mathbb{H}[\mathbb{Q},a,b]$. Then $sk$ applied to the trace of the linear part of $S_m$ (the $2 \times 2$ matrix of coefficients of the degree-one monomials) equals $n$ in $k$.
--
--   This is Drinfeld's trace condition for the formal $\mathcal{O}_D$-module attached to a fake elliptic curve: the trace condition built into the `FakeEllipticCurve` structure, which constrains the action of $\Lambda$ on the tangent space at the identity of a geometric fibre, is transported through the formal coordinates $\theta$ into a statement about the Jacobian matrix at the origin of the pair of power series describing the action of $m$. It feeds into [`CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.isSpecial`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.isSpecial), where the formal module of a fake elliptic curve is shown to be special in Drinfeld's sense.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_trace_linearPart_addVia_eq_of_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (B : Type) [CommRing B]
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k)
    (m : ↥Λ) (n : ℤ) (hm : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    sk (Matrix.trace (MvFormalGroup.linearPart
        (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi)))) = (n : k) := by sorry
