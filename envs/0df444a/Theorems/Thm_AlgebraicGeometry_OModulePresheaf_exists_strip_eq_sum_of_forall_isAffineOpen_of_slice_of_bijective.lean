-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
-- name    : AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/527d3075-75f2-58f7-9fce-4ca2fb19fc6c
-- title:
--   Triviality of strip 1-cocycles when Γ(X)=k
-- statement:
--   Let $k$ be a field and let $f_X : X \to \operatorname{Spec} k$ be quasi-compact and separated, $f_Y : Y \to \operatorname{Spec} k$ separated, with the ring map $k \to \Gamma(X,\mathcal O_X)$ induced by $f_X$ bijective; let $x_0 : \operatorname{Spec} k \to X$ be a section of $f_X$, let $p_1 : P \to X$, $p_2 : P \to Y$ exhibit $P$ as the pullback of $f_X$ and $f_Y$, and let $i_Y : Y \to P$ satisfy $p_1 \circ i_Y = x_0 \circ f_Y$ and $p_2 \circ i_Y = \mathrm{id}_Y$. Let $\mathcal V$ be a `Scheme.OrderedAffineCover` of $Y$: a finite linearly ordered index set $\iota$ together with affine opens $V_i \subseteq Y$ with $\bigsqcup_i V_i = \top$; for a strictly increasing tuple $\sigma : \mathrm{Fin}(i+1) \to \iota$ write $V_\sigma = \bigcap_j V_{\sigma(j)}$, and let $\partial_j \sigma$ denote the tuple obtained by deleting the $j$-th entry. Write $F^U_\sigma = p_1^{-1}U \cap p_2^{-1}V_\sigma$. Assume given, for every affine open $U \subseteq X$ and every increasing pair $\sigma$, a section $e^U_\sigma \in \Gamma(P, F^U_\sigma)$ such that: (cocycle) for every increasing triple $\rho$, $\sum_{j=0}^{2}(-1)^j\, e^U_{\partial_j\rho}|_{F^U_\rho} = 0$; (compatibility) for affine opens $U' \subseteq U$ there are $g_i \in \Gamma(P, F^{U'}_i)$, indexed by the one-element tuples $i$, with $e^U_\sigma|_{F^{U'}_\sigma} - e^{U'}_\sigma = \sum_{j=0}^{1}(-1)^j\, g_{\partial_j\sigma}|_{F^{U'}_\sigma}$ for all increasing pairs $\sigma$; (slice) for every affine open $U$ with $x_0^{-1}U = \top$ there are $g_i \in \Gamma(Y, i_Y^{-1}F^U_i)$ with $i_Y^{\sharp}(e^U_\sigma) = \sum_{j=0}^{1}(-1)^j\, g_{\partial_j\sigma}|_{i_Y^{-1}F^U_\sigma}$ for all $\sigma$. Then for every affine open $U \subseteq X$ there exist $g_i \in \Gamma(P, F^U_i)$ with $e^U_\sigma = \sum_{j=0}^{1}(-1)^j\, g_{\partial_j\sigma}|_{F^U_\sigma}$ for all increasing pairs $\sigma$.
--
--   This is a rigidity statement in Čech form for the structure sheaf on $X \times_k Y$ computed on the strips $p_1^{-1}U \cap p_2^{-1}V_\sigma$: a family of $1$-cocycles, one for each affine open of $X$, compatible up to coboundaries and trivial on the slice $\{x_0\} \times Y$, is trivial over every affine open of $X$. It rests on the degree-zero Künneth identification $\Gamma(P, p_1^{-1}U \cap p_2^{-1}V) \cong \Gamma(X,U) \otimes_k \Gamma(Y,V)$ and on the globalisation of a compatible family of sections of $\mathcal O_X$ over all affine opens when $\Gamma(X,\mathcal O_X) = k$, and is used by [`AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by sorry
