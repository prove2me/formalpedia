-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_9
-- name    : BERicci.Energy.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:27.85318+00:00
-- url     : https://prove2.me/theorems/2fe42b3c-b9f2-45bd-a814-cb9c46488779
-- title:
--   Theorem 3.9 (first sentence), p. 33 — on an Energy measure space the canonical distance d_E satisfies (MD) and (ED)
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space in the sense of Definition 3.6, with truncation profile $S$ as in (3.27); in particular the intrinsic distance $d_{\mathcal E}$ is a finite, complete distance inducing $\tau$. Then $d_{\mathcal E}$ satisfies conditions (MD) and (ED):
--
--   1. $m$ has full support and $m(B_r(x))<\infty$ for every ball of $d_{\mathcal E}$;
--   2. every $\psi\in\mathbb L_C$ is 1-Lipschitz with respect to $d_{\mathcal E}$;
--   3. every $d_{\mathcal E}$-Lipschitz $\psi$ with $|D\psi|\le1$ and bounded support belongs to $\mathbb L_C$.
--
--   $$(X,\tau,m,\mathcal E)\ \text{Energy measure space}\ \Longrightarrow\ d_{\mathcal E}\ \text{satisfies (MD), (ED).}$$
--
--   The theorem places an Energy measure space inside the metric framework of Section 3.1, so that the metric notions (slopes, Cheeger energy, Wasserstein distances) are available for $d_{\mathcal E}$.
--
--   **Formalization Note** The metric of $X$ is $d_{\mathcal E}$ (condition (b) of Definition 3.6), so (MD), (ED.a), (ED.b) are stated for the metric of $X$. Completeness, separability and the Borel σ-algebra of (MD.a) are typeclass binders. The profile $S$ is a parameter with `IsTruncProfile S`, matching the paper's single fixed $S$.
-- source:
--   arXiv:1209.5786v4, Theorem 3.9 (first sentence), p. 33

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.9** (p. 33), first sentence: on an Energy measure space the canonical distance `d_E` (the
metric of `X`, by Definition 3.6 (b)) satisfies (MD) and (ED). -/
theorem theorem_3_9 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S) :
    MD m ∧ EDa m E ∧ EDb m E := by sorry

end BERicci.Energy
