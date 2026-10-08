-- Prove2me | Theorems.Thm_EthierKurtz_oblique_existence_from_apriori_estimate
-- name    : EthierKurtz.oblique_existence_from_apriori_estimate
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T13:30:50.116609+00:00
-- url     : https://prove2.me/theorems/a450f0db-5924-43c9-b1c9-a0a6a9954b2c
-- title:
--   Resolvent existence from the Schauder estimate via continuity
-- statement:
--   This is the existence machine for the oblique-derivative resolvent problem.\n\nUnder the hypotheses of Theorem 1.5, assuming the global Schauder a priori estimate (taken as the explicit hypothesis `hEst`), the method of continuity --- starting from the solvable constant-coefficient oblique base problem --- yields exact resolvent solvability: there is a rate $\\lambda_0 > 0$ such that every H\\\"older right-hand side $h$ is hit exactly, $\\lambda_0 f - g = h$, by a classical pair $(f, g)$ in the reflected graph.\n\nThe estimate hypothesis is stated verbatim as the conclusion of `EthierKurtz.oblique_schauder_apriori_estimate`, so the reduction that applies this machine to that estimate type-checks directly.\n\n**Formalization Note** The conclusion is exactly the target type of `EthierKurtz.oblique_holder_resolvent`; the future proof runs the continuity argument of Gilbarg-Trudinger Theorem 5.2 inside this statement.
-- source:
--   Method of continuity: Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 5, Section 5.2 (Theorem 5.2), with the constant-coefficient oblique base problem; as applied in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Resolvent existence from the Schauder estimate via the method of
continuity: the a priori estimate plus solvability of the constant-
coefficient base problem yields exact solvability for every Hölder
right-hand side. The estimate is taken as an explicit hypothesis so this
is the abstract existence machine of the argument. -/
theorem oblique_existence_from_apriori_estimate (n : ℕ) (hd : 2 ≤ n + 1)
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
      ε ≤ ∑ i, c x i * normal x i)
    (hEst : ∃ lamstar : ℝ, 0 < lamstar ∧ ∃ C₀ : NNReal,
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
                (EuclideanSpace.single i 1)‖)) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c,
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
