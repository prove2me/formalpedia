-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle
-- name    : AlgebraicGeometry.Scheme.Modules.exists_forall_pullback_iso_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/fb796ad8-66f7-532a-a7ff-097042619aa7
-- title:
--   Gluing sheaves of modules along a jointly surjective family of open immersions
-- statement:
--   Let $Y$ be a scheme, $I$ a type, and $X : I \to \mathrm{Scheme}$ a family of schemes equipped with morphisms $\iota_i : X_i \to Y$, each an open immersion, such that the family is jointly surjective on points: for every point $y$ of $Y$ there are an index $i$ and a point $x$ of $X_i$ with $(\iota_i)(x) = y$. Let $M_i$ be a sheaf of modules on $X_i$ for each $i$, and for all $i, j$ let $\varphi_{ij}$ be an isomorphism $p_1^* M_i \cong p_2^* M_j$ of sheaves of modules on the fibre product $X_i \times_Y X_j$, where $p_1, p_2$ are the two projections. Assume the cocycle condition in the following form: for all $i, j, l$, every scheme $T$ and all morphisms $\pi_{12} : T \to X_i \times_Y X_j$, $\pi_{23} : T \to X_j \times_Y X_l$, $\pi_{13} : T \to X_i \times_Y X_l$ satisfying the three compatibilities $\pi_{12} \text{ followed by } p_2 = \pi_{23} \text{ followed by } p_1$, $\pi_{13}$ followed by $p_1$ equals $\pi_{12}$ followed by $p_1$, and $\pi_{13}$ followed by $p_2$ equals $\pi_{23}$ followed by $p_2$, the composite of $\pi_{12}^* \varphi_{ij}$ with $\pi_{23}^* \varphi_{jl}$ on $T$ agrees with $\pi_{13}^* \varphi_{il}$, all three pullbacks being compared by means of the canonical isomorphisms `Scheme.Modules.pullbackComp` for composites and `Scheme.Modules.pullbackCongr` for equal morphisms. The conclusion is that there exist a sheaf of modules $M$ on $Y$ and isomorphisms $\psi_i : \iota_i^* M \cong M_i$ on $X_i$ which induce the given $\varphi_{ij}$: for all $i, j$, on $X_i \times_Y X_j$ the composite of $p_1^*\psi_i$ with $\varphi_{ij}$ equals $p_2^*\psi_j$, again read through the canonical comparison isomorphisms, the identification of the two pullbacks of $M$ being the one attached to the equality $p_1$ followed by $\iota_i$ equals $p_2$ followed by $\iota_j$.
--
--   This is the effectivity of descent data for sheaves of modules along a jointly surjective family of open immersions, i.e. the classical statement that modules given on the members of a Zariski open cover together with cocycle-compatible identifications on the double overlaps glue to a module on the base. The cocycle hypothesis is stated in the representability-free form, tested against an arbitrary scheme $T$ mapping compatibly to the three double overlaps rather than against the triple fibre product; the result is used in the construction of invertible sheaves from charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_pullback_iso_of_cocycle
    {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ y : ↥Y, ∃ (i : I) (x : ↥(X i)), (ι i).base x = y)
    (M : ∀ i, (X i).Modules)
    (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))
    (hcocycle : ∀ (i j l : I) (T : Scheme.{u})
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
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)) :
    ∃ (Mg : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i),
      ∀ i j : I,
        ((Scheme.Modules.pullbackComp (Limits.pullback.fst (ι i) (ι j)) (ι i)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).mapIso (ψ i) ≪≫ φ i j =
          (Scheme.Modules.pullbackCongr
              (Limits.pullback.condition : Limits.pullback.fst (ι i) (ι j) ≫ ι i = Limits.pullback.snd (ι i) (ι j) ≫ ι j)).app Mg ≪≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.snd (ι i) (ι j)) (ι j)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).mapIso (ψ j) := by sorry
