-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/064acb21-1e96-55f3-9426-3c2da98ebf9f
-- title:
--   Pointwise transport of the extra level along a unit twist
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Let $N,m$ be naturals, $S$ a commutative ring, $E$ a fake elliptic curve over $S$ of type $(\Lambda,N)$ — so in particular a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} S$, a commutative relative group law $E.L$ on it and an action $x \mapsto E.\mathrm{act}\,x$ of $\Lambda$ by $E.f$-morphisms — and let $P_1, P$ be two full level-$m$ structures on $E$, $\ell$ a natural number dividing $m$, and $K$ an extra level structure at $\ell$, with level morphism $K.\mathrm{lev}K : K.K \to E.A$. Let $L, L_0 \subseteq \Lambda$ be $\mathbb{Z}$-submodules and $c,d \in \Lambda$ be such that $cd - 1$ and $dc - 1$ both lie in $m\Lambda$ (each equal to $m$ times an element of $\Lambda$), $L_0 c \subseteq L$ and $L d \subseteq L_0$. Let $k$ be an algebraically closed field and $sk : S \to k$ a ring homomorphism, giving the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ induced by $sk$. Assume that the restriction of $P$ to this geometric point is obtained from that of $P_1$ by the action of $c$, and that a section $Q$ over the geometric point factors through $K.\mathrm{lev}K$ (i.e. $Q$ is $P_0$ followed by $K.\mathrm{lev}K$ for some $P_0 : \operatorname{Spec} k \to K.K$) precisely when $Q = x \cdot \bigl(\lfloor m/\ell\rfloor\bigr)$-fold sum of the restriction of $P_1$, for some $x \in \Lambda$ lying in $L$. Then, for every section $Q$ over the geometric point, $Q$ factors through $K.\mathrm{lev}K$ if and only if $Q = x \cdot \bigl(\lfloor m/\ell\rfloor\bigr)$-fold sum of the restriction of $P$, for some $x \in \Lambda$ lying in $L_0$ (the multiple is formed with the group law $E.L$, and natural division is used for $m/\ell$).
--
--   This is the pointwise statement that replacing a full level-$m$ structure by its twist under a unit $c$ modulo $m$ replaces the submodule describing the extra level at $\ell$ by the corresponding translate, the inverse $d$ of $c$ modulo $m$ providing the reverse inclusion. It is used in the construction of a flat surjective cover of the base over which a fake elliptic curve acquires a full level structure compatible with a given extra level, namely by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff), where the twisting unit is only locally constant on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (P₁ P : E.FullLevel m) (ℓ : ℕ) (hℓm : ℓ ∣ m) (K : E.ExtraLevel ℓ)
    (L L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hL₀ : L₀ ≤ Λ)
    (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L)
    (hLd : ∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (hP : FakeEllipticCurve.sectionAt P.P k sk = pushPt (E.act c) (E.act_over c) (FakeEllipticCurve.sectionAt P₁.P k sk))
    (hK : ∀ Q : SchemeHomOver (geomPoint k sk) E.f,
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P₁.P k sk)) = Q)
    (Q : SchemeHomOver (geomPoint k sk) E.f) :
    FactorsThrough K.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q := by sorry
