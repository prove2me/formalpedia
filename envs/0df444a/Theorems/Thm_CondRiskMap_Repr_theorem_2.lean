-- Prove2me | Theorems.Thm_CondRiskMap_Repr_theorem_2
-- name    : CondRiskMap.Repr.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:05.743695+00:00
-- url     : https://prove2.me/theorems/757c6a61-af8c-4f10-865f-132fc0f86d30
-- title:
--   Theorem 2, p. 11 — a positively homogeneous lsc conditional risk mapping is a countable supremum of conditional expectations
-- statement:
--   Let $\Omega$ be a nonempty set with $\sigma$-algebras $\mathcal F_1\subset\mathcal F_2$, and let $\mathcal X_2$ (functions) and $\mathcal Y_2$ (finite signed measures) be paired locally convex spaces satisfying (C) and (C′), with $\mathcal X_2$ separable and containing the indicator $\mathbb 1_A$ of every $A\in\mathcal F_2$. Let $\rho:\mathcal X_2\to\mathcal X_1$ be a positively homogeneous, lower semicontinuous conditional risk mapping, and assume (K). Then there exist probability measures $\nu^i\in\mathcal P_{\mathcal Y_2}$, $i\in\mathbb N$, such that
--   $$
--   \rho_\omega(\cdot)=\sup_{i\in\mathbb N}\mathbb E_{\nu^i}[\,\cdot\,|\mathcal F_1](\omega),\qquad\omega\in\Omega.\qquad(4.9)
--   $$
--   Precisely: there are $\nu^i\in\mathcal P_{\mathcal Y_2}$ and maps $\omega\mapsto\kappa^i_\omega\in\mathcal P_{\mathcal Y_2}$ such that, for each $i$,
--   1. $\omega\mapsto\kappa^i_\omega$ is weakly\* $\mathcal F_1$-measurable;
--   2. $\kappa^i$ is the conditional probability of $\nu^i$ given $\mathcal F_1$: $\omega\mapsto\kappa^i_\omega(A)$ is $\mathcal F_1$-measurable and $\int_S\kappa^i_\omega(A)\,d\nu^i(\omega)=\nu^i(A\cap S)$ for $S\in\mathcal F_1$, $A\in\mathcal F_2$;
--
--   and, with $\mathbb E_{\nu^i}[X|\mathcal F_1](\omega):=\langle\kappa^i_\omega,X\rangle$,
--   $$
--   \rho_\omega(X)=\sup_{i\in\mathbb N}\langle\kappa^i_\omega,X\rangle\quad\text{for all }X\in\mathcal X_2,\ \omega\in\Omega.
--   $$
--
--   This is the converse of the observation that a supremum of conditional expectations is a positively homogeneous conditional risk mapping: under separability and (K), every such mapping arises this way.
--
--   **Formalization Note** A conditional expectation is defined only $\nu$-almost everywhere, while (4.9) holds at every $\omega$; the paper reads $\mathbb E_{\nu}[X|\mathcal F_1](\omega)$ as the integral of $X$ against a conditional probability kernel, and the statement makes this explicit. $\Omega$ is assumed nonempty (for $\Omega=\emptyset$ the hypotheses hold and no probability measure exists). The hypothesis that $\mathcal X_2$ contains all indicators of $\mathcal F_2$-sets is added for the reason given in Proposition 3. Separability is that of the topology of $\mathcal X_2$.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 11, Theorem 2, (4.9)

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴] [Nonempty Ω]
    [TopologicalSpace.SeparableSpace 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) (hI : HasIndicators S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (hK : CondK S ρ) :
    ∃ (ν : ℕ → 𝒴) (κ : ℕ → Ω → 𝒴),
      (∀ i, ν i ∈ Prob S) ∧ (∀ i ω, κ i ω ∈ Prob S) ∧ (∀ i, IsWeakStarMeasurable S (κ i)) ∧
      (∀ i, IsCondProb S (ν i) (κ i)) ∧
      ∀ X ω, IsLUB (Set.range fun i => pair (S.toMeasure (κ i ω)) (S.toFun X)) (ρω S ρ ω X) := by sorry

end CondRiskMap.Repr
