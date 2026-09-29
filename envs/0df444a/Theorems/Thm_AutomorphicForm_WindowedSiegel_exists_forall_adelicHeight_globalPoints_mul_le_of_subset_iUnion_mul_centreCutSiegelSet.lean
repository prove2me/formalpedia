-- Prove2me | Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
-- name    : AutomorphicForm.WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/1325eed4-ab83-5063-a608-738200d6b53d
-- title:
--   Height bound for non-triangular rational translates on Siegel translates
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, let $T_c\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be compact, and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy $\Phi_0\subseteq\bigcup_{y\in T_c}\,(\cdot\,y)\bigl(\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\bigr)$, where the latter set consists of those adelic $g$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` of level-zero integral matrices, whose archimedean component at every infinite place $w$ has local height $\|\det\|/\mathrm{rowNormSq}\ge c$ and window quantity `xWindowSq` at most $u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$. Then there exists $R_1\in\mathbb{R}$ such that for every $x\in\Phi_0$ and every $\gamma\in\mathrm{GL}_2(F)$ with bottom-left entry $\gamma_{10}\neq 0$, the adelic height of $\mathrm{globalPoints}(\gamma)\cdot x$ — the product of $\prod_{w\mid\infty}(\|\det\|/\mathrm{rowNormSq})^{[F_w:\mathbb{R}]}$ at the archimedean component with the finite product of the local factors `finLocalHeight` over the height-one spectrum of $\mathcal{O}_F$ — is at most $R_1$. The proof uses only the integrality and the height-floor conditions $c\le$ local height, discarding the window and determinant constraints.
--
--   This is the height-theoretic form of classical reduction theory for $\mathrm{GL}_2$: above an explicit threshold, a rational translate of a point of $\Phi_0$ can only come from an upper-triangular $\gamma$, since the non-triangular ones all have adelic height bounded by $R_1$. It feeds the estimates on unipotent cells and constant terms used in the analysis of the twisted Bruhat decomposition and of integrals of automorphic forms over translated Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindowedSiegel_exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem
AutomorphicForm.WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 F) F)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet F c u d₁ d₂) :
    ∃ R₁ : ℝ, ∀ x ∈ Φ₀, ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
        NumberField.AdelicHeight.adelicHeight F (globalPoints (𝓞 F) F γ * x) ≤ R₁ := by sorry
