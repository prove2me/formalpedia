-- Prove2me | Theorems.Thm_DurrettProbability_brownian_nowhere_lipschitz
-- name    : DurrettProbability.brownian_nowhere_lipschitz
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-18T18:25:52.442973+00:00
-- url     : https://prove2.me/theorems/ac250682-c43d-421a-9641-d06582c7d6b0
-- title:
--   Theorem 7.1.6 — Brownian paths are nowhere Lipschitz, hence nowhere differentiable
-- statement:
--   Let $B$ be a Brownian motion on a probability space. Then for $\mathbb P$-almost every $\omega$,
--   for **every** time $s\ge0$ and **every** real constant $C$, the path $t\mapsto B_t(\omega)$ is
--   not Lipschitz at $s$ with constant $C$: there is no $\delta>0$ for which
--   $$|B_t(\omega)-B_s(\omega)|\le C\,|t-s|\qquad\text{whenever }|t-s|\le\delta .$$
--
--   Since a function differentiable at $s$ is Lipschitz at $s$ for some constant, this says in
--   particular that almost every Brownian path is differentiable at no point whatsoever.
--
--   **Formalization Note** The order of quantifiers is what makes this the Paley–Wiener–Zygmund
--   theorem rather than a much weaker statement: the null set comes first, so a single path fails
--   the Lipschitz condition simultaneously at every point. The weaker reading — for each fixed $s$,
--   almost surely not Lipschitz at $s$ — would follow from a one-point calculation and is not what
--   is asserted here.
--
--   The constant $C$ ranges over all the reals. For $C<0$ the Lipschitz condition can hold only
--   where the path is locally constant, so its negation is easy there and the content is at
--   $C\ge0$. At $s=0$ the condition is one-sided, the index set being $[0,\infty)$, and the
--   conclusion is asserted there too.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 358 (PDF p. 366), Theorem 7.1.6: 'With probability one, Brownian paths are not Lipschitz continuous (and hence not differentiable) at any point.' Remark on the same page: 'The nondifferentiability of Brownian paths was discovered by Paley, Wiener, and Zygmund (1933). ... The proof we are about to give is due to Dvoretsky, Erdoes, and Kakutani (1961).' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem brownian_nowhere_lipschitz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (C : ℝ), ¬ LipschitzAtPoint (fun t => B t ω) s C := by sorry

end DurrettProbability
