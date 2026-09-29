-- Prove2me | Theorems.Thm_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
-- name    : AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/03caddf6-5673-57e9-a3b0-7469ac606824
-- title:
--   Uniqueness of the weighted orbital integral of a regular semisimple element
-- statement:
--   Let $A$ be a commutative ring carrying a topology making it a Hausdorff, locally compact, second countable topological ring, and equip $\mathrm{GL}_2(A)$ and the centralizer subgroups with their Borel $\sigma$-algebras. Let $\mu$ be a Haar measure on $\mathrm{GL}_2(A)$, let $\gamma \in \mathrm{GL}_2(A)$ be regular semisimple in the sense that $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit of $A$, let $T = \mathrm{Z}(\{\gamma\})$ be the centralizer of $\gamma$ in $\mathrm{GL}_2(A)$ and let $\tau$ be a Haar measure on $T$. Let $\mathrm{wt} \colon \mathrm{GL}_2(A) \to \mathbb{R}$ be continuous and satisfy $\mathrm{wt}(tx) = \mathrm{wt}(x)$ for all $t \in T$ and all $x \in \mathrm{GL}_2(A)$, and let $f \colon \mathrm{GL}_2(A) \to \mathbb{C}$ be Borel measurable and bounded, i.e. $\|f(g)\| \le C$ for some real $C$ and all $g$. Suppose $J_1, J_2 \in \mathbb{C}$ each admit a section function: for $i = 1, 2$ there is $s_i \colon \mathrm{GL}_2(A) \to \mathbb{R}$ which is non-negative, Borel measurable, of compact support, and satisfies $\int_T s_i(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, such that $J_i = \int_{\mathrm{GL}_2(A)} f(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s_i(x)\,d\mu(x)$. Then $J_1 = J_2$.
--
--   This is the well-definedness of the weighted (non-invariant) orbital integral of a regular semisimple element: the truncation by a section function for the centralizer does not affect the value, provided the weight is left invariant under that centralizer. It is the weighted counterpart of the corresponding statement for ordinary orbital integrals, and is used in the archimedean scaling statement for weighted orbital integrals and in the uniqueness statements for diagonal elements at finite places. The argument reduces, via the invariance of $f(x^{-1}\gamma x)\,\mathrm{wt}(x)$ under left translation by the centralizer, to [`MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one`](thm.html#MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one), which compares the integrals of a bounded measurable subgroup-invariant function weighted by two such section functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (wt : GL (Fin 2) A → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), ∀ x : GL (Fin 2) A,
      wt ((t : GL (Fin 2) A) * x) = wt x)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[AutomorphicForm.glBorelOf A] f)
    (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    {J₁ J₂ : ℂ} (h₁ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₁)
    (h₂ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₂) : J₁ = J₂ := by sorry
