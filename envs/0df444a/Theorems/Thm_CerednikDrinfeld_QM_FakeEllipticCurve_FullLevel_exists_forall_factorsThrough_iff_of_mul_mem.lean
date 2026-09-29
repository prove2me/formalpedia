-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_forall_factorsThrough_iff_of_mul_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_forall_factorsThrough_iff_of_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0fdd2075-ec7b-546a-9ed4-91cc41b97ce8
-- title:
--   Twisting a full level structure transports the extra-level line
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Let $N,m$ be natural numbers, $S$ a commutative ring, $E$ a fake elliptic curve over $S$ with multiplications by $\Lambda$ and level $N$, and $P_1$ a full level-$m$ structure on $E$ (an $S$-section of $E.f$ killed by $m$ for the relative group law, generating all $m$-torsion under $\Lambda$ at geometric points, with the stated annihilator condition). Let $\ell\mid m$ and let $K$ be an extra level at $\ell$, with structural morphism `levK` into $E.A$. Let $L,L_0\subseteq\Lambda$ be $\mathbb{Z}$-submodules, and assume that for every algebraically closed field $k'$, every ring map $sk:S\to k'$ and every point $Q$ of $E.f$ over the geometric point determined by $sk$, the point $Q$ factors through `levK` precisely when $Q=x\cdot\bigl((m/\ell)\,P_{1,k'}\bigr)$ for some $x\in L$, where $x$ acts through `E.act` and $(m/\ell)$ is the iterated group law. Assume further that $c,d\in\Lambda$ satisfy $cd-1\in m\Lambda$ and $dc-1\in m\Lambda$, that $xc\in L$ for all $x\in L_0$, and that $xd\in L_0$ for all $x\in L$. Then there is a full level-$m$ structure $P$ on $E$ whose section is the image of that of $P_1$ under `E.act c`, such that at every geometric point as above, $Q$ factors through `levK` precisely when $Q=x\cdot\bigl((m/\ell)\,P_{k'}\bigr)$ for some $x\in L_0$.
--
--   This is the compatibility statement which says that twisting a full level-$m$ structure by $c$ replaces the subset of $\Lambda$ cutting out a given extra level at $\ell$ by a second subset $L_0$ with $L_0c\subseteq L$ and $Ld\subseteq L_0$; the existence of the twisted structure itself comes from [`CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist). It is used in the construction of the moduli tower for fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff) and the subsequent coarse-moduli and Galois-frame statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_forall_factorsThrough_iff_of_mul_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_forall_factorsThrough_iff_of_mul_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (P₁ : E.FullLevel m) (ℓ : ℕ) (hℓm : ℓ ∣ m) (K : E.ExtraLevel ℓ)
    (L L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hL₀ : L₀ ≤ Λ)
    (hK : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : S →+* k') (Q : SchemeHomOver (geomPoint k' sk) E.f),
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt P₁.P k' sk)) = Q)
    (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L)
    (hLd : ∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀) :
    ∃ P : E.FullLevel m, P.P = pushPt (E.act c) (E.act_over c) P₁.P ∧
      ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : S →+* k') (Q : SchemeHomOver (geomPoint k' sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k' sk)) = Q := by sorry
