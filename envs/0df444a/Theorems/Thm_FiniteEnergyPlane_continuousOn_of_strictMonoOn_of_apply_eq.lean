-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousOn_of_strictMonoOn_of_apply_eq
-- name    : FiniteEnergyPlane.continuousOn_of_strictMonoOn_of_apply_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:27:02.470489+00:00
-- url     : https://prove2.me/theorems/af0e297e-7532-44d6-b7f4-0fe2425488c3
-- title:
--   Solutions of a monotone equation depending continuously on a parameter are continuous
-- statement:
--   Let $X$ be a topological space, $S \subseteq X$, and $I \subseteq \mathbb{R}$ open. Let $F : X \times \mathbb{R} \to \mathbb{R}$ be such that $x \mapsto F(x, s)$ is continuous on $S$ for every $s \in I$, and $s \mapsto F(x, s)$ is strictly increasing on $I$ for every $x \in S$. Let $y : X \to \mathbb{R}$ be continuous on $S$, and let $G : X \to \mathbb{R}$ satisfy $G(x) \in I$ and $F(x, G(x)) = y(x)$ for all $x \in S$. Then $G$ is continuous on $S$.
--
--   Role: a parametrized inverse-function statement for monotone equations in one real variable. Only separate continuity of $F$ in the parameter is required.
--
--   Formalization Note: continuity is relative to $S$ (`ContinuousOn`); a strictly decreasing equation is covered by replacing $F$ and $y$ with $-F$ and $-y$.
-- source:
--   Elementary; used in the proof of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9)

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A function `G` solving `F x (G x) = y x`, where each `F x` is strictly increasing on an open set
`I` containing the values of `G`, each `F · s` is continuous and `y` is continuous, is continuous. -/
theorem continuousOn_of_strictMonoOn_of_apply_eq {X : Type*} [TopologicalSpace X] {S : Set X}
    {I : Set ℝ} (hI : IsOpen I) (F : X → ℝ → ℝ)
    (hF : ∀ s ∈ I, ContinuousOn (fun x => F x s) S) (hmono : ∀ x ∈ S, StrictMonoOn (F x) I)
    (G y : X → ℝ) (hG : ∀ x ∈ S, G x ∈ I) (hy : ContinuousOn y S)
    (hFG : ∀ x ∈ S, F x (G x) = y x) : ContinuousOn G S := by
  sorry

end FiniteEnergyPlane
