-- Prove2me | Theorems.Thm_EthierKurtz_oblique_hy_semigroup
-- name    : EthierKurtz.oblique_hy_semigroup
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T12:55:54.79208+00:00
-- url     : https://prove2.me/theorems/d67abb68-8b2b-4881-b288-68a637a301eb
-- title:
--   Hille-Yosida semigroup with exact generator
-- statement:
--   Hille-Yosida semigroup with exact generator.
--
--   Assume the dissipative estimate and the dense-range statement for the closed
--   reflected graph $A$ of Theorem 1.5. Then there exists a strongly continuous
--   contraction semigroup $T$ on $C(\bar\Omega)$ whose generator is exactly $A$:
--
--   $$
--   \lim_{t \downarrow 0} t^{-1}(T_t f - f) = g \iff (f, g) \in A.
--   $$
--
--   This is the abstract generation half of the Hille--Yosida argument: the two
--   resolvent estimates produce the semigroup and identify its generator, before
--   any positivity or conservativeness is established.
--
--   **Formalization Note** Lean takes the two estimates as explicit hypotheses and
--   quantifies $T$ over $\mathbb{R} \to ((closure~\Omega) \to^b~\mathbb{R})
--   \toL[\mathbb{R}] ((closure~\Omega) \to^b~\mathbb{R})$, with convergence in
--   the $\mathcal{N}[>](0)$ filter.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); Hille-Yosida generation with (1.15) and (1.19)--(1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Hille-Yosida semigroup with exact generator: dissipativity plus dense
range for the closed reflected graph produces a strongly continuous
contraction semigroup whose generator is exactly the graph. -/
theorem oblique_hy_semigroup (n : ℕ) (hd : 2 ≤ n + 1)
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
    (hest : ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ,
      0 < delta → ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by sorry
