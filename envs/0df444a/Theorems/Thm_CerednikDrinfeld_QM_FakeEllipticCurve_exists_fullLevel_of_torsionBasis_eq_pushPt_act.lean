-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_of_torsionBasis_eq_pushPt_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7cb720f0-d9cc-5b47-ba64-1a69625f2318
-- title:
--   Torsion basis induced by Λ gives full level-m structure
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated), a natural number $N$, a commutative ring $S$ and a fake elliptic curve $E$ of type $(\Lambda,N)$ over $S$, with structure morphism `E.f`, commutative relative group law `E.L` and $\Lambda$-action `E.act`; fix $m \in \mathbb{N}$. Let $e : \mathrm{Fin}\,4 \to \Lambda$ be a $\mathbb{Z}$-basis of $\Lambda$, in the sense that every $x \in \Lambda$ is an integral combination $\sum_i n_i \cdot e_i$ (hypothesis `hgen`) and such a combination vanishes only for $n = 0$ (`hind`). Let $P$ and $Q_0,\dots,Q_3$ be $S$-points of `E.f` (sections over the identity of $\operatorname{Spec} S$) with $Q_i$ obtained from $P$ by the action of $e_i$, i.e. $Q_i =$ `pushPt (E.act (e i)) _ P`. Assume: each $Q_i$ satisfies $m Q_i = 1$ for the group law; and for every algebraically closed field $k$ and ring homomorphism $s_k : S \to k$, with $Q_i$ restricted along the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$, every $k$-point $R$ killed by $m$ equals $n_0Q_0 + n_1Q_1 + n_2Q_2 + n_3Q_3$ for some $n : \mathrm{Fin}\,4 \to \mathbb{N}$ (the product being formed in that nested order), and any such combination equal to the identity has $m \mid n_i$ for all $i$. The conclusion is that there is a full level-$m$ structure `FL : E.FullLevel m` whose underlying point `FL.P` is $P$: that is, $P$ is killed by $m$, at each geometric point the $m$-torsion is exactly the $\Lambda$-orbit of $P$, and for $x \in \Lambda$ the action of $x$ sends $P$ to the identity precisely when $x = m y$ for some $y \in \Lambda$.
--
--   This is the converse half of the identification of full level-$m$ structures on a fake elliptic curve with $\Lambda$-linear bases of the $m$-torsion: a level structure given by an $S$-point $P$ whose $\Lambda$-translates along a $\mathbb{Z}$-basis of the order form a basis of the $m$-torsion at all geometric points. It is used in the construction of quaternionic moduli data with full level structure on the polarised abelian scheme side, [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField

open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_of_torsionBasis_eq_pushPt_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ)
    (e : Fin 4 → ↥Λ)
    (hgen : ∀ x : ↥Λ, ∃ n : Fin 4 → ℤ, x = ∑ i, n i • e i)
    (hind : ∀ n : Fin 4 → ℤ, ∑ i, n i • e i = 0 → n = 0)
    (Q : Fin 4 → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hQP : ∀ i : Fin 4, Q i = pushPt (E.act (e i)) (E.act_over (e i)) P)
    (hQ :

      (∀ i : Fin 4, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m (Q i) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
        (∀ R : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m R = E.L.one (geomPoint k sk) →
          ∃ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = R) ∧
        (∀ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = E.L.one (geomPoint k sk) →
          ∀ i : Fin 4, m ∣ n i))) :
    ∃ FL : E.FullLevel m, FL.P = P := by sorry
