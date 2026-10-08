-- Prove2me | Theorems.Thm_BERicci_Main_corollary_3_18
-- name    : BERicci.Main.corollary_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:24.879552+00:00
-- url     : https://prove2.me/theorems/c47125cd-63e7-43a5-9fd6-14619b7e3f8e
-- title:
--   Corollary 3.18, p. 42 — $BE(K,\infty)$ and Wasserstein contraction
-- statement:
--   Let $(X,m,\mathcal E)$ be an energy measure space with upper-regular Dirichlet form satisfying $(MD.exp)$, and let $P_t$ be its heat flow. For every $K\in\mathbb R$, the condition $BE(K,\infty)$ is equivalent to the following contraction for every $t\ge0$ and every nonnegative probability densities $f,g\in L^1(X,m)$:
--
--   $$W_2((P_t f)m,(P_t g)m)\le e^{-Kt}W_2(fm,gm).$$
--
--   This identifies the analytic curvature bound with a transport bound on the heat evolution of probability densities.
--
--   **Formalization Note** $P_t$ on $L^1$ is its contractive extension. Lean squares the inequality and uses the extended nonnegative value of $W_2^2$, retaining pairs with infinite transport cost.
-- source:
--   arXiv:1209.5786v4, Corollary 3.18 and (3.48), p. 42

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Main_Regular

namespace BERicci.Main

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Corollary 3.18, p. 42: BE(K,∞) is equivalent to W₂ contraction on probability densities. -/
theorem corollary_3_18 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) [SigmaFinite m]
    (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S) (hUpper : BERicci.Gamma.IsUpperRegular m E)
    (hexp : BERicci.Gamma.MDexp m)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P)
    (P1 : ℝ → (X → ℝ) → X → ℝ) (hP1 : IsL1Extension m P P1)
    (K : ℝ) :
    BERicci.Gamma.BE m E P K 0 ↔
      ∀ t : ℝ, 0 ≤ t → ∀ f g : X → ℝ,
        Integrable f m → Integrable g m →
        0 ≤ᵐ[m] f → 0 ≤ᵐ[m] g →
        (∫ x, f x ∂m) = 1 → (∫ x, g x ∂m) = 1 →
        BERicci.Gamma.W2sq (m.withDensity (fun x => ENNReal.ofReal (P1 t f x)))
            (m.withDensity (fun x => ENNReal.ofReal (P1 t g x))) ≤
          ENNReal.ofReal (Real.exp (-2 * K * t)) *
            BERicci.Gamma.W2sq (m.withDensity (fun x => ENNReal.ofReal (f x)))
              (m.withDensity (fun x => ENNReal.ofReal (g x))) := by sorry

end BERicci.Main
