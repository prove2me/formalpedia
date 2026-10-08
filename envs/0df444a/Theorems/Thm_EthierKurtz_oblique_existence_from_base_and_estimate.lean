-- Prove2me | Theorems.Thm_EthierKurtz_oblique_existence_from_base_and_estimate
-- name    : EthierKurtz.oblique_existence_from_base_and_estimate
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T18:37:30.531134+00:00
-- url     : https://prove2.me/theorems/211c1a39-9bd7-4af0-8833-6ae6fdcf3b74
-- title:
--   Resolvent existence from base solvability and the Schauder estimate
-- statement:
--   This is the abstract assembly step of the continuity argument for the oblique-derivative resolvent problem.\n\nUnder the hypotheses of Theorem 1.5, given both the Laplacian base-case solvability (explicit hypothesis `hBase`) and the Schauder a priori estimate (explicit hypothesis `hEst`), the method of continuity along the interior-coefficient homotopy yields exact resolvent solvability: there is a rate $\\lambda_0 > 0$ such that every H\\\"older right-hand side is hit exactly by a classical pair in the reflected graph.\n\nThe two hypotheses are stated verbatim as the conclusions of `EthierKurtz.oblique_laplacian_base_solvability` and `EthierKurtz.oblique_schauder_apriori_estimate`, so the reduction that supplies them type-checks directly. The future proof builds the homotopy $(1-t)ID + ta$ with the oblique field fixed, re-runs the Schauder estimate uniformly in $t$, and applies the Gilbarg-Trudinger continuity theorem.\n\n**Formalization Note** The conclusion is exactly the target type of `EthierKurtz.oblique_existence_from_apriori_estimate`.
-- source:
--   Method of continuity: Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 5, Section 5.2 (Theorem 5.2), along the interior-coefficient homotopy with fixed oblique boundary condition; as applied in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Resolvent existence from base solvability and the Schauder estimate:
the Laplacian base case plus the a priori estimate feed the method of
continuity along the interior-coefficient homotopy to the full operator.
Both inputs are explicit hypotheses, so this is the abstract assembly
step of the argument. -/
theorem oblique_existence_from_base_and_estimate (n : ℕ) (hd : 2 ≤ n + 1)
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
    (hBase : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h)
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
