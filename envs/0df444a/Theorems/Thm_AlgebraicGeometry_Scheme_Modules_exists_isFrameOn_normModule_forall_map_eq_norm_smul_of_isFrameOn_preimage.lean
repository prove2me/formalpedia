-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e16cfdb1-9dca-5b97-a3f9-09eea9f03d9b
-- title:
--   Frames on the norm module with norm transition functions
-- statement:
--   Let $\pi \colon Y \to X$ be a morphism of schemes, $d$ a natural number, and $(U_i)_{i \in \iota}$ a family of opens of $X$ (no covering or cocycle condition is assumed). For each $i$ let $e_{i,1},\dots,e_{i,d}$ be sections of $\pi_*\mathcal{O}_Y$ over $U_i$, and assume that for every open $W \le U_i$ the restrictions of the $e_{i,k}$ form a $\Gamma(X,W)$-basis of $\Gamma(\pi_*\mathcal{O}_Y, W)$. Let $L$ be an $\mathcal{O}_Y$-module, and for each $i$ let $s_i \in \Gamma(L, \pi^{-1}U_i)$ be a frame on $\pi^{-1}U_i$, i.e. for every open $W \le \pi^{-1}U_i$ the map $g \mapsto g \cdot (s_i|_W)$ from $\Gamma(Y,W)$ to $\Gamma(L,W)$ is bijective. Let $u_{ij} \in \Gamma(Y, \pi^{-1}(U_i \cap U_j))$ satisfy $s_j|_{\pi^{-1}(U_i \cap U_j)} = u_{ij} \cdot s_i|_{\pi^{-1}(U_i \cap U_j)}$. The conclusion asserts the existence of sections $\Omega_i$ of the norm module $\det_d(\pi_*L) \otimes \det_d(\pi_*\mathcal{O}_Y)^{\vee}$ over $U_i$, where $(-)^{\vee}$ is the internal hom into the unit, such that each $\Omega_i$ is a frame on $U_i$ in the same sense, and such that for all pairs $(i,j)$ simultaneously $\Omega_j|_{U_i \cap U_j} = \mathrm{Nm}(u_{ij}) \cdot \Omega_i|_{U_i \cap U_j}$, the norm being taken for the $\Gamma(X, U_i \cap U_j)$-algebra structure on $\Gamma(Y, \pi^{-1}(U_i \cap U_j))$ induced by $\pi$.
--
--   This is the statement that the transition functions of the norm module along a finite locally free morphism of rank $d$ are the norms of the transition functions, in the form of one canonical frame per chart of an arbitrary indexed family of opens. It is used in the comparison of the norm module with tensor powers after pullback and in the construction of a refinement on which the norm module is trivialised with prescribed transition functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage.lean

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

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) {ι : Type u} (U : ι → X.Opens)

    (e : ∀ i, Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U i))
    (he : ∀ (i : ι) (W : X.Opens) (hW : W ≤ U i),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ k, b k = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i k))

    (L : Y.Modules) (s : ∀ i, Γ(L, π ⁻¹ᵁ U i)) (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)))
    (hu : ∀ i j, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s j) =
      u i j • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s i)) :
    ∃ Ω : ∀ i, Γ(Scheme.Modules.normModule π d L, U i),
      (∀ i, Scheme.Modules.IsFrameOn (Ω i) (U i)) ∧
      ∀ i j, letI : Algebra Γ(X, U i ⊓ U j) Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)) := (π.app (U i ⊓ U j)).hom.toAlgebra
        (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op (Ω j) =
          (Algebra.norm Γ(X, U i ⊓ U j) (u i j)) •
            (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op (Ω i) := by sorry
