-- Prove2me | Theorems.Thm_BERicci_Main_theorem_4_16
-- name    : BERicci.Main.theorem_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:34.349668+00:00
-- url     : https://prove2.me/theorems/c3e1c4c6-d805-4799-9129-00b07680f95b
-- title:
--   Theorem 4.16, p. 56 — action and entropy estimate
-- statement:
--   For a regular curve $\rho_s=f_s m$ and $t>0$, set $\rho_{1,t}=H_t\rho_1$. Then
--
--   $$W_2^2(\rho_0,\rho_{1,t})+2t\operatorname{Ent}_m(\rho_{1,t})\le R_K(t)^2\int_0^1|\dot\rho_s|^2\,ds+2t\operatorname{Ent}_m(\rho_0),\qquad R_K(t)=\frac{t}{I_K(t)}.$$
--
--   The estimate controls the heat-evolved endpoint of a regular path using its metric action and initial entropy. It is the quantitative input to the proof of Theorem 4.17.
--
--   **Formalization Note** The action is encoded as the infimum of squared $L^2$ speeds. The inequality is in extended reals, while regularity bounds the starting entropy and action.
-- source:
--   arXiv:1209.5786v4, Theorem 4.16 and (4.29), p. 56

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Contract_Dual
import Definitions.Def_BERicci_Main_Regular

namespace BERicci.Main

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Theorem 4.16, p. 56: the action and entropy estimate for a regular curve. -/
theorem theorem_4_16 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) [SigmaFinite m]
    (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hR : BERicci.Gamma.IsRiemannianEMS m E S) (hexp : BERicci.Gamma.MDexp m)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P)
    (K : ℝ) (hBE : BERicci.Gamma.BE m E P K 0)
    (H : ℝ → Measure X → Measure X) (hH : BERicci.Contract.IsDualSemigroup m P H)
    (P1 : ℝ → (X → ℝ) → X → ℝ) (hP1 : IsL1Extension m P P1)
    (κ : ℝ → ℝ) (hκ : IsTimeMollifier κ)
    (ρ : ℝ → Measure X) (f : ℝ → X → ℝ) (hρ : IsRegularCurve m E P1 κ ρ f)
    (t : ℝ) (ht : 0 < t) :
    BERicci.Gamma.InP2 (H t (ρ 1)) ∧
    ((BERicci.Gamma.W2sq (ρ 0) (H t (ρ 1)) : ℝ≥0∞) : EReal) +
      ((2 * t : ℝ) : EReal) * BERicci.Gamma.entropy m (H t (ρ 1)) ≤
      ((ENNReal.ofReal ((RK K t) ^ 2) * action ρ : ℝ≥0∞) : EReal) +
        ((2 * t : ℝ) : EReal) * BERicci.Gamma.entropy m (ρ 0) := by sorry

end BERicci.Main
