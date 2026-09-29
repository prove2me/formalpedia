-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_field
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/f6fec44b-20f8-514d-a9aa-267937b6daef
-- title:
--   Formal 𝒪_D-coordinates exist over a field where q is nilpotent
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a prime $q$. Let $\mathrm{coord} : \Lambda \to \mathbb{Z}_{q^2} \times \mathbb{Z}_{q^2}$ (with $\mathbb{Z}_{q^2}$ the Witt vectors of $\mathbb{F}_{q^2}$) satisfy `IsOrderCoord`: it is additive, sends $1$ (when $1 \in \Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(x_1,x_2)(y_1,y_2) = (x_1y_1 + q\,x_2\,\sigma(y_2),\ x_1y_2 + x_2\,\sigma(y_1))$ with $\sigma$ the Witt-vector Frobenius, is injective, has image dense in the sense that every pair of residues modulo $q^k$ is attained, and satisfies $(\mathrm{coord}\,m)_1 + \sigma((\mathrm{coord}\,m)_1) = n$ whenever $m + \bar m = n$ for an integer $n$. Let $k$ be a field in which the image of $q$ is nilpotent, and let $E$ be a fake elliptic curve over $k$ with level data $(\Lambda, N)$, i.e. an object of `FakeEllipticCurve Λ N k`. The conclusion asserts the existence of a formal $\mathcal{O}_D$-module $X$ over $k$ — a two-variable commutative formal group law $X.F$ with an action of $\mathbb{Z}_{q^2}$ by one-variable series, together with a series $\varpi$ satisfying $\varpi \circ \varpi = [q]$ and $\varpi \circ [\alpha] = [\sigma(\alpha)] \circ \varpi$ — and of formal coordinates $\theta$ in $2$ variables for the structure morphism $E.f$, assigning to each $k$-algebra $B'$ and each pair $s : \mathrm{Fin}\,2 \to B'$ a section of $E.A$ over $\mathrm{Spec}\,B'$, such that `E.IsFormalModuleVia coord X θ` holds: $\theta$ is a system of formal coordinates for the relative group law $E.L$ with formal group $X.F$ (compatible with $k$-algebra maps, and, for every nilpotent ideal $J$ with $J^{n+1} = 0$, parametrising bijectively the $J$-infinitesimal points and transporting the $n$-truncated group law of $X.F$ to $E.L$), and moreover, for every $k$-algebra $B'$, every ideal $J$ with $J^{n+1} = 0$, every $m \in \Lambda$ and every $s$ with entries in $J$, the coordinate map intertwines the series $\mathrm{addVia}\ X.F\ ([(\mathrm{coord}\,m)_1])\ ([(\mathrm{coord}\,m)_2] \circ \varpi)$, evaluated on $s$ after truncation, with the action of $m$ on $E$ applied to $\theta\,B'\,s$.
--
--   This is the existence of the special formal $\mathcal{O}_D$-module attached to a fake elliptic curve in residue characteristic $q$, compatibly with the action of the quaternionic order through $\mathrm{coord}$; it is the local input of the Čerednik–Drinfel'd description of the bad fibre of a Shimura curve. It is cited by the rigidification and lifting statements for fake elliptic curves over fields and Artinian rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_field.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_field
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (k : Type) [Field k] (hq : IsNilpotent ((q : ℕ) : k)) (E : FakeEllipticCurve Λ N k) :
    ∃ (X : FormalODModule q k) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ := by sorry
