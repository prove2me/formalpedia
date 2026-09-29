-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/7c9ad3fa-3d47-5f50-b4d0-1ea392c24879
-- title:
--   d-torsion of the descended level subgroup has d² points
-- statement:
--   Fix rationals $a,b$, an integral submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $L$ and a fake elliptic curve $E$ of level $N$ with $\Lambda$-action over $L$, together with a finitely generated $\mathbb{Z}$-subalgebra $R \subseteq L$. Over $\operatorname{Spec} R$ one is given a scheme $A_0$ with structure morphism $f_0$, a relative group law $L_0$ on $f_0$ (functorial group operations on sections $T \to A_0$ over a fixed $T \to \operatorname{Spec} R$) which is commutative, and for which $f_0$ is smooth, proper with connected fibres; further a closed immersion $\mathrm{lev}_0 : C_0 \to A_0$ such that the sections factoring through $\mathrm{lev}_0$ are stable under the multiplication and inversion of $L_0$, contain the identity section, and are killed by $N$ in the sense $N \cdot P = 1$; the composite $\mathrm{lev}_0$ followed by $f_0$ is finite, flat and locally of finite presentation, with fibre rank $N^2$ at every point of $\operatorname{Spec} R$. Finally $g : E.A \to A_0$ exhibits $E.f$ as the pullback of $f_0$ along $\operatorname{Spec}$ of the inclusion $R \hookrightarrow L$, compatibly with the two multiplications, and $g_C : E.C \to C_0$ exhibits $E.\mathrm{lev}$ as the pullback of $\mathrm{lev}_0$ along $g$. The conclusion: for every algebraically closed field $k$, every ring homomorphism $s_k : R \to k$ with $N \neq 0$ in $k$, and every $d \mid N$, the set of sections $P$ of $f_0$ over the geometric point $\operatorname{Spec}(s_k) : \operatorname{Spec} k \to \operatorname{Spec} R$ that factor through $\mathrm{lev}_0$ and satisfy $d \cdot P = 1$ has exactly $d^2$ elements.
--
--   This is the point-counting input for the descent of the level structure of a fake elliptic curve from a field $L$ to a finitely generated subring $R$: the $d$-torsion of the descended level subgroup has the same order $d^2$ at every geometric point of $\operatorname{Spec} R$ as it has over $L$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.lev_fibre_descend_of_isPullback_of_fg_of_isCommutative`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.lev_fibre_descend_of_isPullback_of_fg_of_isCommutative), where, combined with a structure theorem for finite abelian groups of this order, it identifies the level subgroup at a geometric point with $(\mathbb{Z}/N)^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L)
    (R : Subalgebra ℤ L) (hR : R.FG)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
    (hcomm₀ : L₀.IsCommutative) (hbundle₀ : AbelianSchemePropertyBundle ↥R f₀)
    (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (hlev_closed₀ : IsClosedImmersion lev₀)
    (hlev_sub₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
    (hlev_one₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
    (hlev_torsion₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
    (hlev_finite₀ : IsFinite (lev₀ ≫ f₀)) (hlev_flat₀ : Flat (lev₀ ≫ f₀)) (hlev_fp₀ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
    (hlev_rank₀ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), (lev₀ ≫ f₀).finrank s = N ^ 2)
    (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (gC : E.C ⟶ C₀) (hgC : CategoryTheory.IsPullback gC E.lev lev₀ g) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R →+* k), (N : k) ≠ 0 →
      ∀ d : ℕ, d ∣ N →
        Nat.card {P : SchemeHomOver (geomPoint k sk) f₀ //
          FactorsThrough lev₀ P ∧ nsmulPt L₀ (geomPoint k sk) d P = L₀.one (geomPoint k sk)} = d ^ 2 := by sorry
