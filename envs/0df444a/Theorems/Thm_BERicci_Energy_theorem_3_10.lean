-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_10
-- name    : BERicci.Energy.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:00.841717+00:00
-- url     : https://prove2.me/theorems/d8d3c50e-73e1-4c10-8292-5952a14d4e85
-- title:
--   Theorem 3.10, p. 34 — the intrinsic distance d_E of an Energy measure space is a length distance
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space. Then $(X,d_{\mathcal E})$ is a length metric space: for all $x_0,x_1\in X$,
--
--   $$d_{\mathcal E}(x_0,x_1)=\inf\Big\{\ell(\gamma):\ \gamma:[0,1]\to X\ \text{continuous},\ \gamma(0)=x_0,\ \gamma(1)=x_1\Big\},\tag{3.2}$$
--
--   where $\ell(\gamma)$ is the length of $\gamma$.
--
--   The length property is what makes the slope and the asymptotic Lipschitz constant interchangeable ((3.4)) and is used in the proof of Proposition 3.11.
--
--   **Formalization Note** The length of a continuous curve is its total variation on $[0,1]$ in $[0,\infty]$; for absolutely continuous curves it equals $\int_0^1|\dot\gamma|\,dr$ of (3.2), and every rectifiable curve can be reparametrized to an absolutely continuous one, so the infimum is the same. The metric of $X$ is $d_{\mathcal E}$.
-- source:
--   arXiv:1209.5786v4, Theorem 3.10, p. 34; (3.2), p. 22

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.10** (p. 34): the canonical distance of an Energy measure space is a length distance (3.2). -/
theorem theorem_3_10 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S) :
    BERicci.Gamma.IsLengthSpace X := by sorry

end BERicci.Energy
