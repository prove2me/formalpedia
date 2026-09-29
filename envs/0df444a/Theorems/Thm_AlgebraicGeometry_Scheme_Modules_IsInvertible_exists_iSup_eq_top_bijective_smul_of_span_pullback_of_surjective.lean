-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/e5eb722e-cf64-5ee7-8548-67b08c6e3992
-- title:
--   Frames of an invertible module descend along a surjective morphism
-- statement:
--   Let $c : X' \to X$ be a surjective morphism of schemes, let $L$ be a module over $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$, and let $\sigma_0,\dots,\sigma_N \in \Gamma(L,\top)$. Let $\sigma'_0,\dots,\sigma'_N \in \Gamma(c^*L,\top)$ be given together with the hypothesis that each $\sigma'_l$ is the image of $\sigma_l$ under the unit of the pullback–pushforward adjunction for $c$, evaluated at $\top$. Suppose further given sections $\rho_0,\dots,\rho_M \in \Gamma(c^*L,\top)$ and opens $U'_0,\dots,U'_M$ of $X'$ whose supremum is $\top$, such that for every $j$ and every open $V' \le U'_j$ the map $\Gamma(X',V') \to \Gamma(c^*L,V')$, $g \mapsto g \cdot (\rho_j|_{V'})$, is bijective, and such that each $\rho_j$ is of the form $\sum_l a_l \cdot \sigma'_l$ for some $a : \mathrm{Fin}(N+1) \to \Gamma(X',\top)$. Then there are opens $U_0,\dots,U_N$ of $X$ with supremum $\top$ such that for every $l$ and every open $V \le U_l$ the map $\Gamma(X,V) \to \Gamma(L,V)$, $g \mapsto g \cdot (\sigma_l|_V)$, is bijective.
--
--   This is the descent step asserting that if the pullbacks of finitely many global sections of an invertible module generate it after a surjective base change — in the strong sense that local frames of the pullback are linear combinations of them — then the sections themselves frame the module on an open cover of the base. It is used in the construction of projective presentations of schemes via invertible modules, in particular in the proof of the existence of a projective presentation compatible with a faithfully flat base change and in the construction of finite towers over fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
    {X X' : Scheme.{u}} (c : X' ⟶ X) [Surjective c]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) {N : ℕ} (σ : Fin (N + 1) → Γ(L, ⊤))

    (σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ l))
    {M : ℕ} (ρ : Fin (M + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (U' : Fin (M + 1) → X'.Opens) (hU' : iSup U' = ⊤)
    (hframe' : ∀ (j : Fin (M + 1)) (V' : X'.Opens), V' ≤ U' j →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback c).obj L).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (ρ j) :
          Γ((Scheme.Modules.pullback c).obj L, V')))
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → Γ(X', ⊤), ρ j = ∑ l, a l • σ' l) :
    ∃ U : Fin (N + 1) → X.Opens, iSup U = ⊤ ∧
      ∀ (l : Fin (N + 1)) (V : X.Opens), V ≤ U l →
        Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l) : Γ(L, V)) := by sorry
