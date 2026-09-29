-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_hom_forall_pullbackSection_eq_zero_iff_and_forall_dualNumber_of_finComb_eq_one
-- name    : AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_and_forall_dualNumber_of_finComb_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/bdfbc856-26fe-5076-a22f-349c4831bc8f
-- title:
--   Translated product section: vanishing at k- and k[ε]-points
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law for $f$: a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over each $t : T \to \operatorname{Spec} k$, natural in $T$. Assume $L$ is commutative and that `AbelianSchemePropertyBundle k f` holds, i.e. $f$ is smooth and proper, every fibre of the underlying map is connected, and a relative group law exists. Let $\mathcal M$ be an $A$-module that is invertible, i.e. locally on $A$ isomorphic to the unit sheaf of modules. Fix $m$, natural numbers $c_i$ and $k$-points $p_i$ ($i \in \operatorname{Fin} m$), that is sections of $f$ over $\mathrm{id}_{\operatorname{Spec} k}$, such that the product $\prod_i p_i^{c_i}$, formed in the group of $k$-points, equals the identity element. Let $\theta_i : \mathbf 1 \to \mathcal M^{\otimes c_i}$ be global sections, where the tensor powers are built by iterated tensoring on the right with $\mathcal M$, and let $\mathcal N$ be an $A$-module equipped with an isomorphism $\mathcal N \cong \mathcal M^{\otimes \sum_i c_i}$. Then there is a global section $s : \mathbf 1 \to \mathcal N$ with the following two properties, where pullback of a global section along $F$ means the canonical section of $F^{*}(-)$ obtained from the inverse of the comparison isomorphism $F^{*}\mathbf 1 \cong \mathbf 1$, and $L.\mathrm{translate}(p_i) : A \to A$ denotes multiplication of the identity section by the constant point $p_i$. First, for every $z : \operatorname{Spec} k \to A$ with $z \circ f = \mathrm{id}$, the pullback of $s$ along $z$ vanishes if and only if for some $i$ the pullback of $\theta_i$ along $z$ followed by $L.\mathrm{translate}(p_i)$ vanishes. Second, for every $T : \operatorname{Spec} k[\varepsilon] \to A$ lying over $\operatorname{Spec}$ of the structure map $k \to k[\varepsilon]$ and every index $i_0$: if for all $i \ne i_0$ the pullback of $\theta_i$ along $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$, followed by $T$ and then by $L.\mathrm{translate}(p_i)$, is nonzero, then the pullback of $s$ along $T$ vanishes if and only if the pullback of $\theta_{i_0}$ along $T$ followed by $L.\mathrm{translate}(p_{i_0})$ vanishes.
--
--   This is the construction, by iterated application of the theorem of the square, of a section of $\mathcal M^{\otimes \sum c_i}$ whose vanishing locus is the union of the translated vanishing loci of the $\theta_i$, together with a clause describing its behaviour on points with values in the dual numbers, where a product of sections of rank-one modules can vanish without any factor vanishing unless all but one factor is a unit at the closed point. It strengthens the corresponding statement about $k$-points alone and is cited by [`AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one`](thm.html#AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one) and by [`AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero`](thm.html#AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero), the latter supplying the tangent-level input to a Lefschetz-type embedding argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_hom_forall_pullbackSection_eq_zero_iff_and_forall_dualNumber_of_finComb_eq_one.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_and_forall_dualNumber_of_finComb_eq_one
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    {m : ℕ} (c : Fin m → ℕ) (p : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hsum : L.finComb (𝟙 (Spec (CommRingCat.of k))) p c = L.one (𝟙 (Spec (CommRingCat.of k))))
    (θ : ∀ i : Fin m, (𝟙_ A.Modules ⟶ 𝓜.tensorPow (c i)))
    (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow (∑ i, c i)) :
    ∃ s : 𝟙_ A.Modules ⟶ 𝓝,
      (∀ (z : Spec (CommRingCat.of k) ⟶ A), z ≫ f = 𝟙 _ →
        (Scheme.Modules.pullbackSection z s = 0 ↔
          ∃ i : Fin m, Scheme.Modules.pullbackSection (z ≫ L.translate (p i)) (θ i) = 0)) ∧
      (∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ A),
        T ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
        ∀ i₀ : Fin m,
          (∀ i : Fin m, i ≠ i₀ →
            Scheme.Modules.pullbackSection
              ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ T) ≫ L.translate (p i)) (θ i) ≠ 0) →
          (Scheme.Modules.pullbackSection T s = 0 ↔
            Scheme.Modules.pullbackSection (T ≫ L.translate (p i₀)) (θ i₀) = 0)) := by sorry
