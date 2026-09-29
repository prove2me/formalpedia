-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_algebraicClosure_rat_of_five_le
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5cc6d20d-f9d1-5548-a378-4b9bfcd724ff
-- title:
--   Fake elliptic curves exist over ℚ̄ when q'≥ 5
-- statement:
--   Let $q$ and $q'$ be distinct primes and let $a,b\in\mathbb Q$ be such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the base change $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans $\mathbb H[\mathbb Q,a,b]$ over $\mathbb Q$, is finitely generated, and every order containing it equals it. Let $N$ be a nonzero natural number divisible by neither $q$ nor $q'$, and assume $5\le q'$. Then the type `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` is nonempty: over $\operatorname{Spec}\overline{\mathbb Q}$ there exist a scheme $A\to\operatorname{Spec}\overline{\mathbb Q}$ with a commutative relative group law, smooth and proper with connected fibres, all fibres of topological Krull dimension $2$, together with morphisms $A\to A$ over the base indexed by $\Lambda$ that are additive and multiplicative in the element of $\Lambda$ (with $\mathrm{act}(xy)=\mathrm{act}(x)\circ\mathrm{act}(y)$), send $1$ to the identity, respect the group law, and act on tangent spaces at geometric points with trace $n$ whenever $m+\bar m=n$, plus the remaining data of the structure, which involve a further scheme $C$ and the level $N$.
--
--   This is the statement that the relevant Shimura curve parametrising abelian surfaces with multiplication by the maximal order $\Lambda$ and level-$N$ structure has a point over $\overline{\mathbb Q}$, i.e. that a fake elliptic curve with these data exists over $\overline{\mathbb Q}$; it is the variant carrying the extra hypothesis $5\le q'$, which makes $2$ and $3$ invertible in the $q'$-adic base used in the argument. It is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat), which removes that hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_algebraicClosure_rat_of_five_le.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_five_le
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hq'5 : 5 ≤ q') :
    Nonempty (FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) := by sorry
