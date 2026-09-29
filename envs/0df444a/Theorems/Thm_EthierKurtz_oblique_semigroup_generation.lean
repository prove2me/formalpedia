-- Prove2me | Theorems.Thm_EthierKurtz_oblique_semigroup_generation
-- name    : EthierKurtz.oblique_semigroup_generation
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T02:16:40.143312+00:00
-- url     : https://prove2.me/theorems/3829e389-d98b-4919-bda1-2708534d4191
-- title:
--   Generation of the reflected semigroup with exact generator
-- statement:
--   Generation of the obliquely reflected semigroup with exact generator.
--
--   Let $\Omega \subset \mathbb{R}^{n+1}$ be a bounded connected open set with
--   $C^{2,\mu}$ boundary, and let $L = \tfrac{1}{2}\sum a_{ij}\partial_{ij} +
--   \sum b_i\partial_i$ be uniformly elliptic with H\"older coefficients.
--   Let $c$ be a $C^{1,\mu}$ reflection field uniformly oblique to the outward
--   unit normal on the boundary, and let $A$ be the closure of the operator graph
--   defined by (1.15) with the oblique boundary condition (1.19)--(1.20). Then
--   there exists a strongly continuous contraction semigroup $T$ on
--   $C(\bar\Omega)$ that is positive ($f \ge 0 \implies T_t f \ge 0$) and
--   conservative ($T_t 1 = 1$), whose generator is exactly $A$:
--
--   $$
--   \lim_{t \downarrow 0} t^{-1}(T_t f - f) = g \iff (f, g) \in A.
--   $$
--
--   This is the existence / Hille--Yosida half of Theorem 1.5: the resolvent of
--   the oblique-derivative elliptic problem inverts $\lambda - A$ on a dense set,
--   and the generated semigroup is identified as the reflected diffusion.
--
--   **Formalization Note** Lean quantifies $T$ over
--   $\mathbb{R} \to ((closure~\Omega) \to^b~\mathbb{R})
--   \toL[\mathbb{R}] ((closure~\Omega) \to^b~\mathbb{R})$ and expresses the
--   generator identity through convergence in the $\mathcal{N}[>](0)$ filter.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); operator equation (1.15) and boundary equations (1.19)--(1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Semigroup generation with exact generator identification: under the
hypotheses of Theorem 1.5, the closed graph is exactly the generator of a
conservative positive strongly continuous contraction semigroup. -/
theorem oblique_semigroup_generation (n : ℕ) (hd : 2 ≤ n + 1)
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
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by sorry
