-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isAtkinLehnerQuotient_comm
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isAtkinLehnerQuotient_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/1c3254c8-8ef1-5ccb-b0af-dff7fb77fb6a
-- title:
--   Atkin–Lehner quotients at q and q' commute
-- statement:
--   Let $N \ge 1$ and let $q \ne q'$ be primes with $q \nmid N$ and $q' \nmid N$. Let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is an order and is maximal among orders. Let $E, E_1, E_{12}, E_2, E_{21}$ be fake elliptic curves of level $N$ with $\Lambda$-action over $\overline{\mathbb{Q}}$ in the sense of the structure `FakeEllipticCurve` (a scheme over $\operatorname{Spec} \overline{\mathbb{Q}}$ with a commutative relative group law, the abelian-scheme property bundle, fibres of dimension $2$, a $\Lambda$-action additive and multiplicative in the required sense and satisfying the trace condition on tangent spaces, together with a level structure $\mathrm{lev}$). Assume $E_1$ is an Atkin–Lehner quotient of $E$ at $q$, $E_{12}$ one of $E_1$ at $q'$, $E_2$ one of $E$ at $q'$, and $E_{21}$ one of $E_2$ at $q$; here `IsAtkinLehnerQuotient r E E'` asks for morphisms $\varphi : E \to E'$ and $\psi : E' \to E$ over the base, both additive on $T$-points and commuting with the $\Lambda$-actions, such that whenever $r \in \Lambda$ the composites $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ are the actions of $r$ on $E$ and on $E'$, such that a $T$-point $P$ of $E$ is killed by $\varphi$ precisely when $m \cdot P$ is the identity for every $m \in \Lambda$ with $m \bar m$ an integer multiple of $r$, and such that $\varphi$ carries points factoring through $\mathrm{lev}_E$ to points factoring through $\mathrm{lev}_{E'}$. The conclusion is `Iso E₁₂ E₂₁`: there is an isomorphism of schemes $E_{12} \cong E_{21}$ over $\operatorname{Spec} \overline{\mathbb{Q}}$ which is additive on $T$-points, commutes with the $\Lambda$-actions, and for which a $T$-point factors through the level structure of $E_{12}$ if and only if its image factors through that of $E_{21}$.
--
--   This is the commutativity, up to isomorphism of fake elliptic curves with level structure, of the two Atkin–Lehner quotient constructions at the two primes where the indefinite quaternion algebra ramifies. It is used in the verification of the compatibility laws for the moduli tower, via [`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isAtkinLehnerQuotient_comm.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isAtkinLehnerQuotient_comm
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E E₁ E₁₂ E₂ E₂₁ : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (h₁ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient q E E₁) (h₁₂ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient q' E₁ E₁₂)
    (h₂ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient q' E E₂) (h₂₁ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient q E₂ E₂₁) :
    QM.FakeEllipticCurve.Iso E₁₂ E₂₁ := by sorry
