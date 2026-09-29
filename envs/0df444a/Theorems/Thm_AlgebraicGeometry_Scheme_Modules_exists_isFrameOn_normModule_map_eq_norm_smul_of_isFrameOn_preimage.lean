-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/179921e2-4e8e-55e2-94e3-5cfc56e69169
-- title:
--   Frames of N_π(L) with transition function Nm(u)
-- statement:
--   Let $\pi\colon Y\to X$ be a morphism of schemes, let $d$ be a natural number, and let $\mathcal U$ be a two-affine open cover of $X$, that is, two affine opens $U_0,U_1\subseteq X$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Suppose given, for $i=0,1$, a family $e_i\colon \mathrm{Fin}\,d\to\Gamma(\pi_*\mathcal O_Y,U_i)$ (sections of the pushforward along $\pi$ of the unit object of $Y$'s modules) such that for every open $W\le U_i$ there is a $\Gamma(X,W)$-basis of $\Gamma(\pi_*\mathcal O_Y,W)$ indexed by $\mathrm{Fin}\,d$ whose $j$-th member is the restriction of $e_i(j)$ to $W$. Let $L$ be an $\mathcal O_Y$-module, and let $s_0\in\Gamma(L,\pi^{-1}U_0)$, $s_1\in\Gamma(L,\pi^{-1}U_1)$ be frames in the sense of `IsFrameOn`: for every open $W\le\pi^{-1}U_i$ the map $g\mapsto g\cdot (s_i|_W)$ from $\Gamma(Y,W)$ to $\Gamma(L,W)$ is bijective. Let $u\in\Gamma(Y,\pi^{-1}(U_0\sqcap U_1))$ satisfy $s_1|_{\pi^{-1}(U_0\sqcap U_1)}=u\cdot s_0|_{\pi^{-1}(U_0\sqcap U_1)}$. Then, for the $\Gamma(X,U_0\sqcap U_1)$-algebra structure on $\Gamma(Y,\pi^{-1}(U_0\sqcap U_1))$ given by the component of $\pi$ at $U_0\sqcap U_1$, there exist sections $\Omega_0$ over $U_0$ and $\Omega_1$ over $U_1$ of $N_\pi(L)=\det_d(\pi_*L)\otimes(\det_d(\pi_*\mathcal O_Y))^\vee$, each a frame on its open in the same sense, with $\Omega_1|_{U_0\sqcap U_1}=\mathrm{Nm}(u)\cdot\Omega_0|_{U_0\sqcap U_1}$, where $\mathrm{Nm}$ is the algebra norm of $u$ over $\Gamma(X,U_0\sqcap U_1)$.
--
--   This is the two-chart cocycle description of the norm of a line bundle along $\pi$ (EGA IV, 21.5): a module glued from frames by the transition function $u$ has norm glued from frames by $\mathrm{Nm}(u)$. It is used in the study of the relative Picard functor, being cited by [`AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul`](thm.html#AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul), where the norm of a unit of the form $1+\varepsilon a$ is computed via the trace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) (𝒰 : X.TwoAffineOpenCover)
    (e₀ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U0))
    (he₀ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U0),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U1))
    (he₁ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₁ i))
    (L : Y.Modules) (s₀ : Γ(L, π ⁻¹ᵁ 𝒰.U0)) (s₁ : Γ(L, π ⁻¹ᵁ 𝒰.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (π ⁻¹ᵁ 𝒰.U0)) (hs₁ : Scheme.Modules.IsFrameOn s₁ (π ⁻¹ᵁ 𝒰.U1))
    (u : Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)))
    (hs : L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op s₁ =
      u • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op s₀) :
    letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom.toAlgebra
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule π d L, 𝒰.U0)) (Ω₁ : Γ(Scheme.Modules.normModule π d L, 𝒰.U1)),
      Scheme.Modules.IsFrameOn Ω₀ 𝒰.U0 ∧ Scheme.Modules.IsFrameOn Ω₁ 𝒰.U1 ∧
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) u) •
          (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by sorry
