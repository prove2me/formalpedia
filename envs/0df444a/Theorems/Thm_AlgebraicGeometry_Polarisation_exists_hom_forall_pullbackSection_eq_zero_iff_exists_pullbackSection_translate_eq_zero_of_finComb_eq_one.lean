-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one
-- name    : AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/50340732-6ada-57ae-a455-5de0de002dc2
-- title:
--   Translated sections multiply when sum cᵢ pᵢ = 0
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of sections over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$, compatible with base change; assume $L$ is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that every fibre of $f$ is connected, and that a relative group law for $f$ exists. Let $\mathcal M$ be a module on $A$ that is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal M$ is isomorphic to the unit sheaf of $U$. Let $m \in \mathbb N$, let $c : \operatorname{Fin} m \to \mathbb N$, and let $p_i$ ($i \in \operatorname{Fin} m$) be $k$-points of $A$, i.e. morphisms $\operatorname{Spec} k \to A$ splitting $f$, such that the product $\prod_i p_i^{c_i}$, formed in the group of $k$-points attached to $L$ via `finComb`, is the neutral element. Let $\theta_i : \mathbf 1 \to \mathcal M^{\otimes c_i}$ be global sections, where $\mathcal M^{\otimes n}$ denotes the $n$-fold tensor power built by iterated tensoring on the right, and let $\mathcal N$ be a module on $A$ together with an isomorphism $\mathcal N \cong \mathcal M^{\otimes \sum_i c_i}$. Then there exists a global section $s : \mathbf 1 \to \mathcal N$ such that for every $k$-point $z$ of $A$ the pullback of $s$ along $z$ vanishes if and only if, for some $i$, the pullback of $\theta_i$ along $z$ followed by the translation endomorphism $L.\mathrm{translate}(p_i)$ of $A$ vanishes.
--
--   This is the divisor-free form, for a commutative abelian scheme over an algebraically closed field, of the statement that when $\sum_i c_i p_i = 0$ the translated theta sections $T_{p_i}^{*}\theta_i$ multiply to a global section of $\mathcal M^{\otimes \sum_i c_i}$ whose zero locus on $k$-points is the union of the translated zero loci; it rests on the theorem of the square. It is used in the comparison of morphisms to projective space built from such sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one.lean

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

theorem AlgebraicGeometry.Polarisation.exists_hom_forall_pullbackSection_eq_zero_iff_exists_pullbackSection_translate_eq_zero_of_finComb_eq_one
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    {m : ℕ} (c : Fin m → ℕ) (p : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hsum : L.finComb (𝟙 (Spec (CommRingCat.of k))) p c = L.one (𝟙 (Spec (CommRingCat.of k))))
    (θ : ∀ i : Fin m, (𝟙_ A.Modules ⟶ 𝓜.tensorPow (c i)))
    (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow (∑ i, c i)) :
    ∃ s : 𝟙_ A.Modules ⟶ 𝓝, ∀ (z : Spec (CommRingCat.of k) ⟶ A), z ≫ f = 𝟙 _ →
      (Scheme.Modules.pullbackSection z s = 0 ↔
        ∃ i : Fin m, Scheme.Modules.pullbackSection (z ≫ L.translate (p i)) (θ i) = 0) := by sorry
