-- Prove2me | Theorems.Thm_EthierKurtz_oblique_schauder_apriori_estimate
-- name    : EthierKurtz.oblique_schauder_apriori_estimate
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T13:30:36.059627+00:00
-- url     : https://prove2.me/theorems/9877ba46-a83c-487e-aaae-b1ab665e0f36
-- title:
--   Global Schauder a priori estimate for the oblique resolvent problem
-- statement:
--   This is the global Schauder a priori estimate for the oblique-derivative resolvent problem.\n\nUnder the hypotheses of Theorem 1.5 (bounded connected $C^{2,\\mu}$ region, uniformly elliptic operator with H\\\"older coefficients, uniformly oblique $C^{1,\\mu}$ reflection field), there are a threshold rate $\\lambda^* > 0$ and a constant $C_0$ such that every classical solution pair $(f, g)$ of $\\lambda f - g = h$ with $\\lambda \\ge \\lambda^*$ and H\\\"older data $h$ (constant $C_h$) satisfies a uniform bound on the full $C^{2,\\mu}$ norm-sum of $f$ --- value, gradient, and Hessian --- with constant $C_0 (C_h + 1)$, in both sup and H\\\"older form.\n\nThis is the analytic input to the method of continuity: it supplies the uniform estimate along the homotopy from the constant-coefficient base problem to the full operator.\n\n**Formalization Note** Second partials use the project idiom `fderiv \\u211d (fun y => fderiv \\u211d F y (single j 1)) x (single i 1)` with `F := closedRegionRestriction f`, as in `CTwiceHolder`; the norm-sum is one real-valued function on `closure \\u03a9`, bounded in sup and in `HolderWith`, which controls every component.
-- source:
--   Global Schauder a priori estimate for the oblique derivative problem: Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 6 (global Schauder estimates, including the oblique derivative problem); the estimate invoked for (1.15) in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Global Schauder a priori estimate for the oblique resolvent problem:
above a threshold rate, every classical solution pair for Hölder data has
its full C^{2,μ} norm-sum (value, gradient, Hessian) bounded uniformly by
the Hölder constant of the data. This is the analytic input to the method
of continuity. -/
theorem oblique_schauder_apriori_estimate (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∃ lamstar : ℝ, 0 < lamstar ∧ ∃ C₀ : NNReal,
      ∀ (f h : (closure Ω) →ᵇ ℝ) (Ch : NNReal) (lam : ℝ),
        lamstar ≤ lam →
        HolderWith Ch ⟨μ, hμ.1.le⟩ ⇑h →
        (∃ g : (closure Ω) →ᵇ ℝ,
          (f, g) ∈ obliqueDiffusionGraph Ω μ a b c ∧ lam • f - g = h) →
        (∀ x : closure Ω,
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖ ≤
            ↑(C₀ * (Ch + 1))) ∧
        HolderWith (C₀ * (Ch + 1)) ⟨μ, hμ.1.le⟩ (fun x : closure Ω =>
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖) := by sorry

end EthierKurtz
