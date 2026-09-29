-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/48cb24ec-0fa4-5822-80d2-7970e6b77ecb
-- title:
--   Geometric fibres of the descended level subgroup are (ℤ/N)²
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, a commutative ring $L$ and a fake elliptic curve $E$ of the type `FakeEllipticCurve Λ N L`. Let $R\subseteq L$ be a finitely generated $\mathbb Z$-subalgebra, let $f_0 : A_0\to\operatorname{Spec} R$ be a morphism of schemes carrying a relative group law $L_0$ — a functorial group structure, natural in the base change, on the sections $\{\varphi : T\to A_0 \mid \varphi\text{ followed by }f_0 = t\}$ for each $t : T\to\operatorname{Spec} R$ — which is commutative, and suppose $f_0$ is smooth, proper, with connected fibres and admits a relative group law. Let $\mathrm{lev}_0 : C_0\to A_0$ be a closed immersion such that, for every base $t : T\to\operatorname{Spec} R$, the sections factoring through $\mathrm{lev}_0$ contain the unit, are stable under $L_0$-multiplication and inversion, and are killed by $N$ (the $N$-fold iterate `nsmulPt` of a factoring section is the unit), and such that $\mathrm{lev}_0$ followed by $f_0$ is finite, flat, locally of finite presentation and of fibre rank $N^2$ at every point of $\operatorname{Spec} R$. Assume further $g : E.A\to A_0$ makes a pullback square with $E.f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R\hookrightarrow L$, that $g$ carries $L_0$-multiplication of sections to $E$'s, and that $g_C : E.C\to C_0$ makes a pullback square with $E.\mathrm{lev}$, $\mathrm{lev}_0$ and $g$. Then for every algebraically closed field $k$ and every ring homomorphism $s_k : R\to k$ with $N\neq 0$ in $k$, there is a bijection $\mathbb Z/N\times\mathbb Z/N \to \{P \text{ a section of } f_0 \text{ over } \operatorname{Spec}(s_k) \mid P \text{ factors through } \mathrm{lev}_0\}$ sending sums to $L_0$-products.
--
--   This is the statement that the descended level-$N$ subgroup scheme $C_0\subseteq A_0$ over the finitely generated stage $R$ has full level structure at every geometric point of $\operatorname{Spec} R$ at which $N$ is invertible: its geometric points form a group isomorphic to $(\mathbb Z/N)^2$. It is used in the passage from a fake elliptic curve over a general base ring $L$ to one over a finitely generated subalgebra, where the level condition must be recovered for the descended datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_lev_fibre_descend_of_isPullback_of_fg_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
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
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f₀ // FactorsThrough lev₀ P},
        ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f₀) = L₀.mul (geomPoint k sk) (e x) (e y) := by sorry
