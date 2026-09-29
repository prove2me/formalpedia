-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a4c2c13f-e33f-52cd-8e78-2003820781f6
-- title:
--   Frames for the norm module after refining the cover
-- statement:
--   Let $\pi\colon X\to Y$ be a morphism of schemes that is finite, flat, locally of finite presentation and surjective, with $X$ and $Y$ integral, and assume that $\Gamma(Y,U)$ is integrally closed for every affine open $U\subseteq Y$. Let $d$ be a natural number with $\pi$ of fibre rank $\pi.\mathrm{finrank}\,y = d$ at every $y\in Y$. Let $Nf$ assign to each open $W\subseteq Y$ a map $\Gamma(X,\pi^{-1}W)\to\Gamma(Y,W)$ which is unital and multiplicative, commutes with the restriction maps of both structure sheaves along any inclusion $W'\le W$, and, on every affine open $W$ for which $\Gamma(X,\pi^{-1}W)$ is a finite free module over $\Gamma(Y,W)$ via $\pi$, coincides with $\mathrm{Algebra.norm}$. Let $U\colon\iota\to Y.\mathrm{Opens}$ be a family of opens of $Y$ indexed by a type in the same universe, $L$ an $\mathcal O_X$-module, and $s_i\in\Gamma(L,\pi^{-1}U_i)$ sections such that each $s_i$ is a frame on $\pi^{-1}U_i$, i.e. for every open $W\le\pi^{-1}U_i$ the map $g\mapsto g\cdot s_i|_W$ from $\Gamma(X,W)$ to $\Gamma(L,W)$ is bijective; let $u_{ij}\in\Gamma(X,\pi^{-1}(U_i\sqcap U_j))$ satisfy $s_j|_{\pi^{-1}(U_i\sqcap U_j)} = u_{ij}\cdot s_i|_{\pi^{-1}(U_i\sqcap U_j)}$. Then there exist a type $\kappa$ in the same universe, opens $T_k\subseteq Y$ and an index map $r\colon\kappa\to\iota$ with $\bigsqcup_k T_k=\bigsqcup_i U_i$ and $T_k\le U_{r(k)}$, together with sections $\Omega_k\in\Gamma(N_\pi(L),T_k)$ of the norm module $N_\pi(L)=\det{}_d(\pi_*L)\otimes(\det{}_d(\pi_*\mathcal O_X))^\vee$ (the dual being the internal hom into the unit object), such that each $\Omega_k$ is a frame on $T_k$ and, on $T_k\sqcap T_l$, $\Omega_l|_{T_k\sqcap T_l} = Nf_{U_{r(k)}\sqcap U_{r(l)}}(u_{r(k)r(l)})|_{T_k\sqcap T_l}\cdot\Omega_k|_{T_k\sqcap T_l}$, the restriction of the norm being taken along the inclusion $T_k\sqcap T_l\le U_{r(k)}\sqcap U_{r(l)}$.
--
--   This is the cocycle computation underlying the norm of an invertible module along a finite locally free morphism onto a normal integral base: local frames of $L$ with transition functions $u_{ij}$ produce, after passing to a refinement of the cover, local frames of $\det_d(\pi_*L)\otimes(\det_d(\pi_*\mathcal O_X))^\vee$ whose transition functions are the norms $Nf(u_{ij})$. It is used in the construction of the norm of an invertible module and the identification of its pullback, via [`AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [Surjective π]
    [IsIntegral X] [IsIntegral Y] (hN : ∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U))
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)

    (Nf : ∀ W : Y.Opens, Γ(X, π ⁻¹ᵁ W) → Γ(Y, W))
    (h1 : ∀ W : Y.Opens, Nf W 1 = 1 ∧ ∀ a b : Γ(X, π ⁻¹ᵁ W), Nf W (a * b) = Nf W a * Nf W b)
    (h2 : ∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
      Nf W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) = Y.presheaf.map (homOfLE h).op (Nf W a))
    (h3 : ∀ (W : Y.Opens), IsAffineOpen W →
      letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
      ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
      ∀ a : Γ(X, π ⁻¹ᵁ W), Nf W a = Algebra.norm Γ(Y, W) a)

    {ι : Type u} (U : ι → Y.Opens) (L : X.Modules) (s : ∀ i, Γ(L, π ⁻¹ᵁ U i))
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(X, π ⁻¹ᵁ (U i ⊓ U j)))
    (hu : ∀ i j, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s j) =
      u i j • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s i)) :
    ∃ (κ : Type u) (T : κ → Y.Opens) (r : κ → ι), (⨆ k, T k) = ⨆ i, U i ∧ (∀ k, T k ≤ U (r k)) ∧
      ∃ Ω : ∀ k, Γ(Scheme.Modules.normModule π d L, T k),
        (∀ k, Scheme.Modules.IsFrameOn (Ω k) (T k)) ∧
        ∀ (k l : κ) (hkl : T k ⊓ T l ≤ U (r k) ⊓ U (r l)),
          (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op (Ω l) =
            Y.presheaf.map (homOfLE hkl).op (Nf (U (r k) ⊓ U (r l)) (u (r k) (r l))) •
              (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op (Ω k) := by sorry
