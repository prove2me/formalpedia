-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_iso_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_iso_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d085fe39-1866-5ae0-b6ae-e355c8ef6aa3
-- title:
--   Atkin–Lehner quotients transport along isomorphisms of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, a natural number $r$, and four objects $E,E',F,F'$ of type `QM.FakeEllipticCurve Λ N S`, each consisting of a scheme over $\operatorname{Spec} S$ carrying a commutative relative group law, the abelian-scheme property bundle (smooth, proper, connected fibres, group law present), two-dimensional fibres, an action of $\Lambda$ by endomorphisms over $S$ that are homomorphisms for the group law, additive and anti-multiplicative in $\Lambda$ and satisfying the trace condition, together with its level datum `lev`. Assume `IsAtkinLehnerQuotient r E E'`: there are morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ over $S$, each a homomorphism on $T$-points and commuting with the $\Lambda$-actions, such that whenever the image of $r$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$ one has $\psi \circ \varphi = E.\mathrm{act}(r)$ and $\varphi \circ \psi = E'.\mathrm{act}(r)$; such that a $T$-point $P$ of $E$ is killed by $\varphi$ exactly when $\mathrm{act}(m)$ kills $P$ for every $m \in \Lambda$ with $m\,\overline{m} = rn$ for some integer $n$; and such that $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$. Assume further `Iso E F` and `Iso E' F'`, i.e. isomorphisms of the underlying schemes over $S$ that are homomorphisms on $T$-points, commute with the $\Lambda$-actions, and match the factorisations through the respective `lev`. Then `IsAtkinLehnerQuotient r F F'` holds.
--
--   This is the invariance of the Atkin–Lehner quotient relation at $r$ under isomorphism of fake elliptic curves on both sides, a transport-of-structure step in the moduli formalism for Čerednik–Drinfeld uniformisation. It is used in the companion equivalence between Atkin–Lehner quotients and isomorphisms, and in the identification of Hecke neighbours and of Atkin–Lehner involutions in the moduli tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_iso_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S] (r : ℕ)
    (E E' F F' : QM.FakeEllipticCurve Λ N S)
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E')
    (hE : QM.FakeEllipticCurve.Iso E F) (hE' : QM.FakeEllipticCurve.Iso E' F') :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r F F' := by sorry
