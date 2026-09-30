-- Prove2me | Theorems.Thm_EthierKurtz_oblique_semigroup_positive_of_resolvent
-- name    : EthierKurtz.oblique_semigroup_positive_of_resolvent
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T13:48:43.109607+00:00
-- url     : https://prove2.me/theorems/376cf2cd-c47c-4779-9521-f24f92268392
-- title:
--   Semigroup positivity from resolvent positivity
-- statement:
--   Semigroup positivity from resolvent positivity.
--
--   Let $T$ be a strongly continuous contraction semigroup on
--   $C(\bar\Omega)$ whose generator is exactly the closed reflected graph $A$
--   of Theorem 1.5. If the graph satisfies the resolvent positivity estimate,
--   then $T$ preserves nonnegativity:
--
--   $$
--   f \ge 0 \implies T_t f \ge 0 \qquad (t \ge 0).
--   $$
--
--   This is the abstract transfer half: the exponential formula builds the
--   semigroup out of positive resolvents, so positivity passes from the
--   resolvent to the semigroup.
--
--   **Formalization Note** Lean takes the graph resolvent estimate as an explicit
--   hypothesis alongside the semigroup and its generator identity.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); exponential formula for the semigroup.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Semigroup positivity from resolvent positivity: a strongly continuous
contraction semigroup whose generator is exactly the closed reflected graph
preserves nonnegativity whenever the graph itself satisfies the resolvent
positivity estimate, via the exponential formula. -/
theorem oblique_semigroup_positive_of_resolvent (n : ℕ) (hd : 2 ≤ n + 1)
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
    (T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ))
    (hT : IsStronglyContinuousContractionSemigroup T)
    (hgen : ∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c))
    (hres : ∀ fg ∈ obliqueDiffusionGraph Ω μ a b c, ∀ lam : ℝ, 0 < lam →
      (∀ x, 0 ≤ (lam • fg.1 - fg.2) x) → ∀ x, 0 ≤ fg.1 x) :
    ∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x := by sorry
