-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_9_converse
-- name    : BERicci.Energy.theorem_3_9_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:52.721286+00:00
-- url     : https://prove2.me/theorems/d7ac7a76-3e88-4d6e-b06b-69da1376489c
-- title:
--   Theorem 3.9 (converse), p. 33 — a distance with (MD) and (ED) makes (X, τ, m, E) an Energy measure space, and d = d_E (3.29)
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ as in (2.1), and let $d$ be a distance on $X$ inducing the topology $\tau$ and satisfying conditions (MD) and (ED). Let $S$ be a truncation profile as in (3.27). Then $(X,\tau,m,\mathcal E)$ is an Energy measure space (Definition 3.6) and
--
--   $$d(x_1,x_2)=d_{\mathcal E}(x_1,x_2)\qquad\text{for every }x_1,x_2\in X.\tag{3.29}$$
--
--   Together with the first sentence of Theorem 3.9, this characterizes Energy measure spaces as the structures in which some distance satisfies (MD) and (ED), the distance then being necessarily $d_{\mathcal E}$.
--
--   **Formalization Note** The distance $d$ is the metric of $X$ and $\tau$ its topology; the printed "distance on $X\times X$" is read as a distance on $X$. Completeness, separability and the Borel σ-algebra of (MD.a) are typeclass binders. Condition (a) of Definition 3.6 involves the fixed profile $S$, which is a parameter with `IsTruncProfile S`. The identity (3.29) is also part of `IsEnergyMeasureSpace`; it is stated again as a separate conjunct.
-- source:
--   arXiv:1209.5786v4, Theorem 3.9 (second sentence), (3.29), p. 33

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.9** (p. 33), converse: if `E` is a strongly local Dirichlet form and the metric `d` of `X`
(inducing the topology `τ`) satisfies (MD) and (ED), then `(X, τ, m, E)` is an Energy measure space, which
includes `d = d_E` (3.29). -/
theorem theorem_3_9_converse {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hMD : MD m) (hEDa : EDa m E) (hEDb : EDb m E) :
    BERicci.Gamma.IsEnergyMeasureSpace m E S ∧ ∀ x₁ x₂ : X, edist x₁ x₂ = BERicci.Gamma.intrinsicDist m E x₁ x₂ := by sorry

end BERicci.Energy
