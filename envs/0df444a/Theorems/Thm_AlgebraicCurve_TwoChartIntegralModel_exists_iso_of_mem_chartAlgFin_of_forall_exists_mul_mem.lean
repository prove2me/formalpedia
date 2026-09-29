-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/55ba4b2a-c4ed-5ca1-8e56-3e29e9e72ce7
-- title:
--   Comparable two-chart integral models are isomorphic over R
-- statement:
--   Let $R$ be a commutative ring, $F$ a field with an $R$-algebra structure, and $j,j'$ nonzero elements of $F$. For a parameter $t$ write $A_{\mathrm{fin}}(t)=$ `chartAlgFin R F t` for the subalgebra of elements of $F$ integral over $R[t]$ and $A_\infty(t)=$ `chartAlgInf R F t` for the elements integral over $R[t^{-1}]$; [`AlgebraicCurve.TwoChartIntegralModel R F t`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the scheme obtained as the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions of these two chart algebras into the middle algebra, and `toBase R F t` is the induced morphism to $\operatorname{Spec} R$. Assume both models, for $j$ and for $j'$, are integral schemes, both morphisms `toBase` are separated, and both $A_\infty(j)$, $A_\infty(j')$ are $R$-algebras of finite type. Assume further $j'\in A_{\mathrm{fin}}(j)$ and $j\in A_{\mathrm{fin}}(j')$, and mutual elementwise visibility: every $y\in A_\infty(j')$ has $sy\in A_\infty(j)$ for some $s\in A_\infty(j)$ of the shape $s=1+j^{-1}a$ with $a\in A_\infty(j)$, and symmetrically with the roles of $j$ and $j'$ exchanged. The conclusion provides an isomorphism of schemes $w$ between the two models, an $R$-algebra homomorphism $\iota_F\colon A_{\mathrm{fin}}(j')\to A_{\mathrm{fin}}(j)$, an element $s\in A_\infty(j)$ and an $R$-algebra homomorphism $\psi\colon A_\infty(j')\to A_\infty(j)[1/s]$ such that: $\iota_F$ is the identity on underlying elements of $F$ and is bijective; $s=1+j^{-1}a$ for some $a\in A_\infty(j)$ (with $j^{-1}$ taken as the element `jInvChartInf R F j` of $A_\infty(j)$); for every $y\in A_\infty(j')$ there are $n\in\mathbb N$ and $z\in A_\infty(j)$ with $s^n y=z$ in $F$ and $\psi(y)\cdot s^n=z$ in $A_\infty(j)[1/s]$; $w$ followed by `toBase R F j'` equals `toBase R F j`; the chart morphism `ιFin R F j` followed by $w$ equals $\operatorname{Spec}(\iota_F)$ followed by `ιFin R F j'`; and $\operatorname{Spec}$ of the localisation map $A_\infty(j)\to A_\infty(j)[1/s]$ followed by `ιInf R F j` and then by $w$ equals $\operatorname{Spec}(\psi)$ followed by `ιInf R F j'`.
--
--   This is the rigidity statement for two-chart integral models: two such models built inside one field $F$ from parameters whose chart algebras are mutually comparable are isomorphic over $\operatorname{Spec} R$, by an isomorphism which is the identity on the common finite chart and is given on a neighbourhood $D(s)$ of the poles by a map of pole charts. It is obtained from the one-sided comparison lemma [`AlgebraicCurve.TwoChartIntegralModel.exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem) and is used for the identification of models and for the construction of the Atkin–Lehner type involution in the Deligne–Rapoport model constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j')]
    [IsSeparated (toBase R F j)] [IsSeparated (toBase R F j')]
    [Algebra.FiniteType R (chartAlgInf R F j)] [Algebra.FiniteType R (chartAlgInf R F j')]
    (hfin : j' ∈ chartAlgFin R F j) (hfin' : j ∈ chartAlgFin R F j')
    (hvis : ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hvis' : ∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F j',
      (∃ a ∈ chartAlgInf R F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j')
      (ιF : chartAlgFin R F j' →ₐ[R] chartAlgFin R F j)
      (s : chartAlgInf R F j) (ψ : chartAlgInf R F j' →ₐ[R] Localization.Away s),
      (∀ x, (ιF x : F) = x) ∧ Function.Bijective ιF ∧
      (∃ a : chartAlgInf R F j, s = 1 + jInvChartInf R F j * a) ∧
      (∀ y : chartAlgInf R F j', ∃ (n : ℕ) (z : chartAlgInf R F j), (s : F) ^ n * (y : F) = z ∧
        ψ y * algebraMap _ (Localization.Away s) (s ^ n) = algebraMap _ (Localization.Away s) z) ∧
      w.hom ≫ toBase R F j' = toBase R F j ∧
      ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j' ∧
      Spec.map (CommRingCat.ofHom (algebraMap (chartAlgInf R F j) (Localization.Away s))) ≫ ιInf R F j ≫ w.hom =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιInf R F j' := by sorry
