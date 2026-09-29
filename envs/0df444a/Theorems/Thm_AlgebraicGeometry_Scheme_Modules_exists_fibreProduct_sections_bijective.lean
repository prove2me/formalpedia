-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
-- name    : AlgebraicGeometry.Scheme.Modules.exists_fibreProduct_sections_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e5d8cc57-cffc-5271-ab0a-93ed10685225
-- title:
--   Sections of a fibre product of mathcal O_X-modules
-- statement:
--   Let $X$ be a scheme, let $N_0$, $N_1$, $N_{01}$ be $\mathcal O_X$-modules (objects of `X.Modules`), and let $a : N_0 \to N_{01}$ and $b : N_1 \to N_{01}$ be morphisms of $\mathcal O_X$-modules. The assertion is that there exist an $\mathcal O_X$-module $L$ and morphisms $\pi_0 : L \to N_0$, $\pi_1 : L \to N_1$ such that, first, $\pi_0$ followed by $a$ equals $\pi_1$ followed by $b$; second, for every open $U \subseteq X$ the map $\Gamma(L,U) \to \Gamma(N_0,U) \times \Gamma(N_1,U)$ sending $s$ to $(\pi_{0,U}(s), \pi_{1,U}(s))$ is injective; and third, for every open $U$ and all sections $s_0 \in \Gamma(N_0,U)$, $s_1 \in \Gamma(N_1,U)$ with $a_U(s_0) = b_U(s_1)$ in $\Gamma(N_{01},U)$ there is a section $s \in \Gamma(L,U)$ with $\pi_{0,U}(s) = s_0$ and $\pi_{1,U}(s) = s_1$. In other words, $L$ is a fibre product of $a$ and $b$ whose sections over each open set are, via $(\pi_0,\pi_1)$, in bijection with the set-theoretic fibre product $\Gamma(N_0,U) \times_{\Gamma(N_{01},U)} \Gamma(N_1,U)$.
--
--   This is the statement that fibre products of sheaves of modules on a scheme are computed sectionwise over each open set; it packages the pullback of $\mathcal O_X$-modules together with the concrete description of its sections. It is used to glue a module from modules given on two opens together with an identification on the intersection, and is cited in the construction of extensions of morphisms of modules along open immersions and in the treatment of invertible sheaves on two-chart affine open covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_fibreProduct_sections_bijective
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by sorry
