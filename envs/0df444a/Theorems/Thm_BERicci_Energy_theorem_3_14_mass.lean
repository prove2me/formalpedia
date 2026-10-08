-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_14_mass
-- name    : BERicci.Energy.theorem_3_14_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:10.002372+00:00
-- url     : https://prove2.me/theorems/14e3ffc8-3ca1-4b8a-bf88-4635e1f2de84
-- title:
--   Theorem 3.14 (mass preservation), p. 38 — for upper-regular E with (MD.exp), the heat flow (P_t) is mass preserving (2.12)
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space with $\mathcal E$ upper-regular, and let $(P_t)_{t\ge0}$ be the heat flow of $\mathcal E$. If moreover (MD.exp) holds, i.e. there are $x_0\in X$, $M>0$, $c\ge0$ with $m(B_r(x_0))\le Me^{cr^2}$ for every $r\ge0$, then $(P_t)$ is mass preserving:
--
--   $$\int_XP_tf\,dm=\int_Xf\,dm\qquad\text{for every }f\in L^1(X,m),\ t\ge0.\tag{2.12}$$
--
--   Mass preservation (stochastic completeness) is a standing assumption of several later results of the paper; this clause shows that it is automatic in the metric framework under the growth condition (MD.exp).
--
--   **Formalization Note** The heat flow is a binder `P` pinned by `IsHeatSemigroup m E P`, which characterizes it uniquely. Since it acts on $L^2$, (2.12) is stated for $f\in L^1\cap L^2$, which determines the $L^1$ extension by density and $L^1$-contractivity. The conclusion includes $P_tf\in L^1$, so that the integral is not the default value of a non-integrable function.
-- source:
--   arXiv:1209.5786v4, Theorem 3.14 (last sentence), p. 38; (2.12), p. 13; (MD.exp), p. 21

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.14** (p. 38), last sentence: if `E` is upper-regular and (MD.exp) holds, the heat flow
`(P_t)` is mass preserving (2.12), stated on `L¹ ∩ L²`, with `P_t f ∈ L¹` made explicit. -/
theorem theorem_3_14_mass {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P)
    (hUR : BERicci.Gamma.IsUpperRegular m E) (hexp : BERicci.Gamma.MDexp m)
    (f : X → ℝ) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (P t f) m ∧ ∫ x, P t f x ∂m = ∫ x, f x ∂m := by sorry

end BERicci.Energy
