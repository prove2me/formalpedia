-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_relIndex_eq_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_relIndex_eq_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/cdb25b56-d7e9-5b5e-ab6e-8f3ada75c2a5
-- title:
--   Lattice between ℓΛ and Λ of index ℓ² cutting out an extra level
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Let $N,m$ be natural numbers, $k$ an algebraically closed field with $m$ invertible in $k$, $E$ a fake elliptic curve over $k$ of type $(\Lambda,N)$ — an abelian scheme $E.f : E.A \to \operatorname{Spec} k$ with commutative relative group law $E.L$, two-dimensional fibres, and an action $x \mapsto E.\mathrm{act}\,x$ of $\Lambda$ over the base, together with the further data recorded in the structure — and $P$ a full level-$m$ structure on $E$, and let $\ell \mid m$ and let $K$ be an extra level at $\ell$ on $E$, given by a closed immersion $K.\mathrm{lev}_K : K.K \to E.A$ whose points form a $\Lambda$-stable subgroup killed by $\ell$, finite flat of rank $\ell^2$ with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$. Then there is a $\mathbb{Z}$-submodule $L \subseteq \mathbb{H}[\mathbb{Q},a,b]$ such that $L \le \Lambda$, $(\ell:\mathbb{Q})\cdot x \in L$ for all $x \in \Lambda$, $L$ is stable under left multiplication by elements of $\Lambda$, the relative index of the additive group of $L$ in that of $\Lambda$ equals $\ell^2$, and for every algebraically closed field $k'$ in the same universe, every ring homomorphism $sk : k \to k'$ and every point $Q$ of $E.A$ over the geometric point $\operatorname{Spec} k' \to \operatorname{Spec} k$ induced by $sk$: $Q$ factors through $K.\mathrm{lev}_K$ (that is, $Q$ is $P_0$ followed by $K.\mathrm{lev}_K$ for some $P_0 : \operatorname{Spec} k' \to K.K$) if and only if there is $x \in \Lambda$ with $x \in L$ such that the image under $E.\mathrm{act}\,x$ of the $(m/\ell)$-fold multiple of the base change of $P$ to $k'$ equals $Q$.
--
--   This identifies an extra level-$\ell$ structure on a fake elliptic curve carrying a full level-$m$ structure with a left-$\Lambda$-stable lattice $L$ with $\ell\Lambda \subseteq L \subseteq \Lambda$ of relative index $\ell^2$, the geometric points of the extra level being exactly the translates $x\cdot\frac{m}{\ell}P$ for $x \in L$. It is used in the construction of full level structures on curves with extra level and in the analysis of the moduli tower of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_relIndex_eq_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_relIndex_eq_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (hm : (m : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m) (ℓ : ℕ) (hℓm : ℓ ∣ m) (K : E.ExtraLevel ℓ) :
    ∃ L : Submodule ℤ ℍ[ℚ, a, b], L ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L) ∧
      L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧
      ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k' sk)) = Q := by sorry
