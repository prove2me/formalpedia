-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_algebraicClosure_rat_of_isIndefiniteRamifiedExactlyAt_two_three
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_isIndefiniteRamifiedExactlyAt_two_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/a4dc131f-5b14-5d0f-892f-1166d1a05211
-- title:
--   Fake elliptic curves of discriminant 6 over ℚ̄
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra. Assume `IsIndefiniteRamifiedExactlyAt a b 2 3`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $v$ contains $2$ or contains $3$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, finitely generated, spans $B$ over $\mathbb{Q}$, and every order containing $\Lambda$ equals $\Lambda$. Let $N$ be a nonzero natural number divisible by neither $2$ nor $3$. The conclusion is that the type `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` is nonempty: over $k=\overline{\mathbb{Q}}$ there is a scheme $A$ with a structure morphism $f\colon A\to\operatorname{Spec} k$, a commutative relative group law on $f$, the abelian-scheme property bundle for $f$ (smooth, proper, connected fibres, a group law exists), all fibres of topological Krull dimension $2$, an action of $\Lambda$ by $k$-endomorphisms of $A$ that is additive, sends $1$ to the identity, satisfies $\mathrm{act}(xy)=\mathrm{act}(y)$ followed by $\mathrm{act}(x)$, is compatible with the group law, and whose trace on any tangent-space model equals the reduced trace $m+\bar m$, together with the remaining data of the structure (among them a scheme $C$) recording the level-$N$ structure.
--
--   This supplies the existence of fake elliptic curves with full level-$N$ structure over $\overline{\mathbb{Q}}$ in the remaining discriminant-$6$ case, where both ramified primes are small; it is the input cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat), which assembles the cases of ramification at two primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_algebraicClosure_rat_of_isIndefiniteRamifiedExactlyAt_two_three.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_algebraicClosure_rat_of_isIndefiniteRamifiedExactlyAt_two_three
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b 2 3)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (h2N : ¬ 2 ∣ N) (h3N : ¬ 3 ∣ N) :
    Nonempty (FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) := by sorry
