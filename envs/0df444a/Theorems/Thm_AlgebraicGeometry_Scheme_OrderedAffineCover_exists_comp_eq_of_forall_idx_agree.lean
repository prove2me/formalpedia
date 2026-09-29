-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/11051042-ed74-57d8-96ad-a01ecd1a3b36
-- title:
--   Gluing chart morphisms along a nilpotent thickening
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings whose kernel $I = \ker \pi$ is a nilpotent ideal ($I^n = 0$ for some $n$). Let $p \colon P \to \operatorname{Spec} T'$ be separated, let $p_0 \colon P_0 \to \operatorname{Spec} T$ and $G \colon P_0 \to P$ form a cartesian square with $p$ and $\operatorname{Spec}(\pi)$, and let $f \colon A \to \operatorname{Spec} T'$ and $\mu \colon P_0 \to A$ be given. Let $\mathcal{W}$ consist of a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq P$, each affine, with $\bigsqcup_i U_i = P$. Assume given, for each $i$, a morphism $m_i \colon U_i \to A$ such that the restriction $G\!\mid_{U_i} \colon G^{-1}U_i \to U_i$ followed by $m_i$ equals the inclusion $G^{-1}U_i \hookrightarrow P_0$ followed by $\mu$; and, for each $0$-simplex $t$ of $\mathcal{W}$ (a strictly monotone $\operatorname{Fin} 1 \to \iota$, so a single index $t_0$, with $\mathcal{W}.\mathrm{inter}\,t = U_{t_0}$), a morphism $v_t \colon \operatorname{Spec}\Gamma(P, U_{t_0}) \to A$ over $\operatorname{Spec} T'$, i.e. $v_t$ followed by $f$ is $\operatorname{Spec}$ of the $T'$-algebra structure map of $\Gamma(P, U_{t_0})$ coming from $p$, such that $v_t$ agrees with the composite of the inverse of the canonical isomorphism $U_{t_0} \cong \operatorname{Spec}\Gamma(P, U_{t_0})$, the inclusion into $U_{t_0}$ and $m_{t_0}$ after precomposition with $\operatorname{Spec}$ of the quotient by $I\,\Gamma(P, U_{t_0})$. Assume finally that for each $1$-simplex $s$ (a pair $i < j$ in $\iota$), the two morphisms $\operatorname{Spec}\Gamma(P, U_i \cap U_j) \to A$ obtained from $v$ at the two faces of $s$ by $\operatorname{Spec}$ of the $T'$-algebra restriction maps agree. Then there exists $m' \colon P \to A$ with $m'$ followed by $f$ equal to $p$ and $G$ followed by $m'$ equal to $\mu$. No compatibility of $m'$ with the individual $m_i$ or $v_t$ is asserted.
--
--   This is the gluing step that converts chart-by-chart data over a nilpotent thickening into a single global morphism: the affine charts of an ordered affine cover carry morphisms to $A$ over $\operatorname{Spec} T'$ which agree on edges and which reduce to the given morphism $\mu$ on the closed subscheme $P_0$. It is used in the construction of lifts of relative group laws and of morphisms of abelian schemes from cocycle data, where the obstruction has been trivialised chartwise; the identification of $G^{-1}U$ with the spectrum of $\Gamma(P,U)$ modulo $I\,\Gamma(P,U)$ is supplied by [`AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq`](thm.html#AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) [IsSeparated p]
    (p₀ : P₀ ⟶ Spec (CommRingCat.of T)) (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) (μ : P₀ ⟶ A)
    (𝒲 : P.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmμ : ∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ)
    (v : ∀ t : 𝒲.Idx 0, Spec (CommRingCat.of Γ(P, 𝒲.inter t)) ⟶ A)
    (hvf : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      v t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, 𝒲.inter t))))
    (hvm : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter p 𝒲 t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫ v t)
    (hagree : ∀ s : 𝒲.Idx 1, letI := algebraOfHom p (𝒲.inter s)
      letI := algebraOfHom p (𝒲.inter (𝒲.face s 0)); letI := algebraOfHom p (𝒲.inter (𝒲.face s 1))
      Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 1)).toRingHom) ≫ v (𝒲.face s 1) =
        Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 0)).toRingHom) ≫ v (𝒲.face s 0)) :
    ∃ m' : P ⟶ A, m' ≫ f = p ∧ G ≫ m' = μ := by sorry
