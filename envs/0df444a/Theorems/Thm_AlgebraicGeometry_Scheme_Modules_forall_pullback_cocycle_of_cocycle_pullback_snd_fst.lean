-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_pullback_cocycle_of_cocycle_pullback_snd_fst
-- name    : AlgebraicGeometry.Scheme.Modules.forall_pullback_cocycle_of_cocycle_pullback_snd_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a3d11fdd-6a5c-5155-999d-ca4902b36f6c
-- title:
--   Cocycle condition over arbitrary test schemes from universal triple overlap
-- statement:
--   Let $Y$ be a scheme, $I$ a type, $X_i$ ($i \in I$) schemes equipped with morphisms $\iota_i : X_i \to Y$, and for each $i$ let $M_i$ be a sheaf of modules on $X_i$. Suppose given, for all $i,j$, an isomorphism $\varphi_{ij} : p_1^{*}M_i \cong p_2^{*}M_j$ of sheaves of modules on the fibre product $X_i \times_Y X_j$, where $p_1,p_2$ are its two projections. The hypothesis is that for all $i,j,l$, on the scheme $P = (X_i\times_Y X_j)\times_{X_j}(X_j\times_Y X_l)$ formed from $p_2 : X_i\times_Y X_j \to X_j$ and $p_1 : X_j\times_Y X_l \to X_j$, and for every morphism $\pi_{13} : P \to X_i\times_Y X_l$ whose composites with the two projections of $X_i\times_Y X_l$ agree with the corresponding composites through the two projections of $P$, the cocycle identity holds: the composite built from $\varphi_{ij}$ pulled back along the first projection of $P$, the defining square equality of $P$, and $\varphi_{jl}$ pulled back along the second projection of $P$ equals the pullback of $\varphi_{il}$ along $\pi_{13}$, both read as isomorphisms on $P$ through the coherence isomorphisms `Scheme.Modules.pullbackComp` (pullback along a composite) and `Scheme.Modules.pullbackCongr` (pullback along equal morphisms). The conclusion is the same identity over an arbitrary test scheme: for all $i,j,l$, every scheme $T$ and morphisms $\pi_{12} : T \to X_i\times_Y X_j$, $\pi_{23} : T \to X_j\times_Y X_l$, $\pi_{13} : T \to X_i\times_Y X_l$ with $\pi_{12}\,$ followed by $p_2$ equal to $\pi_{23}$ followed by $p_1$, and with $\pi_{13}$ compatible with $\pi_{12}$ and $\pi_{23}$ on the first and second factors respectively, the two corresponding composites of isomorphisms on $T$, from the pullback of $M_i$ along $\pi_{12}$ followed by $p_1$ to the pullback of $M_l$ along $\pi_{13}$ followed by $p_2$, coincide.
--
--   This is the standard reduction in descent for sheaves of modules: the cocycle condition on a gluing datum need only be checked on the universal triple overlap $(X_i\times_Y X_j)\times_{X_j}(X_j\times_Y X_l)$, since any other triple of compatible projections factors through it. It is used in the construction of an invertible sheaf on $Y$ from charts together with rigidifying data, [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_forall_pullback_cocycle_of_cocycle_pullback_snd_fst.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.forall_pullback_cocycle_of_cocycle_pullback_snd_fst
    {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y)
    (M : ∀ i, (X i).Modules)
    (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))
    (h0 : ∀ (i j l : I) (π₁₃ : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶ Limits.pullback (ι i) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)) :
    ∀ (i j l : I) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l) := by sorry
