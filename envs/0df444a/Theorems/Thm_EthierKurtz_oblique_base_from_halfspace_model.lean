-- Prove2me | Theorems.Thm_EthierKurtz_oblique_base_from_halfspace_model
-- name    : EthierKurtz.oblique_base_from_halfspace_model
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T20:04:03.787991+00:00
-- url     : https://prove2.me/theorems/29959a12-094f-43fa-ab0d-3c665e38de73
-- title:
--   Base solvability from the half-space model via localization
-- statement:
--   This is the localization assembly that turns the half-space model into global base-case solvability.\n\nOn a bounded connected $C^{2,\\mu}$ region with a $C^{1,\\mu}$ uniformly oblique field, assuming the half-space model solvability (explicit hypothesis `hModel`), the base Laplacian resolvent problem is exactly solvable for every H\\\"older right-hand side. The future proof straightens the boundary via the $C^{2,\\mu}$ charts, freezes the oblique field at each boundary point to reach the constant-direction model, patches the local solutions with a partition of unity, and controls the errors with the uniform Schauder estimates imported from `EthierKurtz.oblique_schauder_apriori_estimate`.\n\nThe model hypothesis is stated verbatim as the conclusion of `EthierKurtz.oblique_halfspace_model_solvability`, so the reduction that supplies it type-checks directly.\n\n**Formalization Note** The conclusion is exactly the target type of `EthierKurtz.oblique_laplacian_base_solvability`.
-- source:
--   Boundary flattening, freezing the oblique field, and patching local half-space solutions via partition of unity, with uniform Schauder estimates; cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 6, and Lieberman on oblique derivative problems; as used in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Base solvability from the half-space model via localization: flattening
the C^{2,μ} boundary, freezing the oblique field, and patching local
half-space solutions turns the model problem into global base-case
solvability. The model is an explicit hypothesis; uniform Schauder
estimates enter through the imported estimate theorem. -/
theorem oblique_base_from_halfspace_model (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (hModel : ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (h : (closure {x : EuclideanSpace ℝ (Fin (n + 1)) |
        (0 : ℝ) < x (0 : Fin (n + 1))}) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph
          {x : EuclideanSpace ℝ (Fin (n + 1)) |
            (0 : ℝ) < x (0 : Fin (n + 1))} μ (fun _ => 1) (fun _ => 0)
          (fun _ => EuclideanSpace.single (0 : Fin (n + 1)) (-1 : ℝ)),
          lam₀ • fg.1 - fg.2 = h) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
