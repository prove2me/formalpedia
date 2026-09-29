-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_essSup_exists
-- name    : CondConvexRisk.Representation.essSup_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:54:17.84486+00:00
-- url     : https://prove2.me/theorems/0d5094cc-f701-446b-a268-3af1f3a6de8c
-- title:
--   Theorem A.1 — existence and uniqueness of the essential supremum
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mathcal X=\{X_i\}_{i\in I}$ a family of extended random variables. Then:
--   1. there exists $X^*\in D(\mathcal X)$ with $X^*\le Z$ $P$-a.s. for every $Z\in D(\mathcal X)$, i.e. an essential supremum $X^*=\operatorname{ess.sup}\mathcal X$;
--   2. it is unique up to $P$-null sets;
--   3. if $I\neq\emptyset$ and $\mathcal X$ is upward directed, there is a sequence $(i_n)$ in $I$ such that
--   $$X_{i_n}\nearrow X^*\quad P\text{-a.s.}$$
--
--   The essential supremum replaces the pointwise supremum, which is not measurable and not well defined on equivalence classes for uncountable families; part 3 is what makes monotone convergence applicable to it.
--
--   **Formalization Note** Members are $P$-a.e. measurable functions $\Omega\to$ `EReal`. The nonemptiness of $I$ in part 3 is added: for the empty family no sequence exists (the paper's statement tacitly assumes a nonempty family).
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 19, Theorem A.1 (proof cited to [8] Föllmer–Schied, Stochastic Finance (2002), Theorem A.18)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem essSup_exists {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P) :
    (∃ Z : Ω → EReal, IsEssSup P F Z) ∧
    (∀ Z Z' : Ω → EReal, IsEssSup P F Z → IsEssSup P F Z' → Z =ᵐ[P] Z') ∧
    (Nonempty ι → IsUpwardDirected P F → ∀ Z : Ω → EReal, IsEssSup P F Z →
      ∃ s : ℕ → ι, ∀ᵐ ω ∂P, Monotone (fun n => F (s n) ω) ∧
        Tendsto (fun n => F (s n) ω) atTop (𝓝 (Z ω))) := by sorry

end CondConvexRisk.Representation
