-- Prove2me | Theorems.Thm_EthierKurtz_oblique_semigroup_conservative
-- name    : EthierKurtz.oblique_semigroup_conservative
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T13:18:07.243682+00:00
-- url     : https://prove2.me/theorems/b115dd1b-a770-41be-a5df-7ed7488a71ce
-- title:
--   Conservativeness of the reflected semigroup
-- statement:
--   Conservativeness of the reflected semigroup.
--
--   Let $T$ be a strongly continuous contraction semigroup on
--   $C(\bar\Omega)$ whose generator is exactly the closed reflected graph $A$
--   of Theorem 1.5. Then $T$ fixes the constant function one:
--
--   $$
--   T_t 1 = 1 \qquad (t \ge 0).
--   $$
--
--   Constants are annihilated by the interior operator and satisfy the oblique
--   boundary condition, so $(1, 0)$ lies in the graph; the generator identity
--   then forces the semigroup to preserve constants along its trajectories.
--
--   **Formalization Note** Lean quantifies over all $T$ with the semigroup
--   property and the generator identity, concluding $T_t 1 = 1$ for nonnegative
--   times.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); constants in the graph (1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Conservativeness of the reflected semigroup: any strongly continuous
contraction semigroup whose generator is exactly the closed reflected graph
fixes the constant function one, since constants are annihilated by the
interior operator and satisfy the oblique boundary condition. -/
theorem oblique_semigroup_conservative (n : ℕ) (hd : 2 ≤ n + 1)
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
        (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c)) :
    ∀ t : ℝ, 0 ≤ t → T t 1 = 1 := by sorry
