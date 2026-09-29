-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP
-- name    : CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/50fecb80-1031-5440-bffd-287c609e8e1a
-- title:
--   Level-one fake elliptic curves exist in characteristic q
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, let $a, b \in \mathbb{Q}$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. that $a > 0$ or $b > 0$ and that, for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q}, a, b]$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is the only order containing it. Let $k$ be an algebraically closed field of characteristic $q$. The conclusion is that the type `FakeEllipticCurve Λ 1 k` is nonempty, i.e. there is a scheme $A$ with a morphism $f \colon A \to \operatorname{Spec} k$ carrying a commutative relative group law $L$ on the functor of points over $\operatorname{Spec} k$, with $f$ smooth and proper with connected fibres, all fibres of topological Krull dimension $2$, together with an action $x \mapsto \operatorname{act} x$ of $\Lambda$ by endomorphisms of $A$ over $\operatorname{Spec} k$ which is unital, multiplicative, additive and compatible with $L$ on points, and which satisfies the trace condition: whenever the tangent space at the identity over a geometric point is realised as a finite-dimensional vector space $V$ with the induced $k$-linear endomorphism $\Phi$ of $m \in \Lambda$, and $m + \bar m = n$ with $n \in \mathbb{Z}$, then $\operatorname{tr}_k(\Phi) = n$ in $k$; plus the further data of the structure constituting a level-$1$ structure.
--
--   This is the existence of a base point for the Čerednik–Drinfeld uniformisation of the Shimura curve attached to $\Lambda$ at the ramified prime $q$: fake elliptic curves of level one over an algebraically closed field of characteristic $q$, obtained from supersingular elliptic curves with quaternionic multiplication. It feeds the corresponding statement with level structures, [`CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_of_isAlgClosed_of_charP`](thm.html#CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_of_isAlgClosed_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] :
    Nonempty (FakeEllipticCurve Λ 1 k) := by sorry
