-- Prove2me | Theorems.Thm_EthierKurtz_oblique_hille_yosida_generation
-- name    : EthierKurtz.oblique_hille_yosida_generation
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:33:02.718771+00:00
-- url     : https://prove2.me/theorems/97e61e02-006a-470f-9744-94c734f50388
-- title:
--   Hille-Yosida generation from the resolvent estimates
-- statement:
--   Hille--Yosida generation from the resolvent estimates.
--
--   Assume the dissipative estimate and the dense-range statement for the closed
--   reflected graph $A$ of Theorem 1.5. Then there exists a strongly continuous
--   contraction semigroup $T$ on $C(\bar\Omega)$ that is positive
--   ($f \ge 0 \implies T_t f \ge 0$) and conservative ($T_t 1 = 1$), whose
--   generator is exactly $A$:
--
--   $$
--   \lim_{t \downarrow 0} t^{-1}(T_t f - f) = g \iff (f, g) \in A.
--   $$
--
--   This is the generation step itself: the two resolvent estimates produce the
--   semigroup by the Hille--Yosida theorem, while positivity and conservativeness
--   follow from the maximum principle for the interior operator together with the
--   oblique boundary condition.
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

/-- Hille-Yosida generation from the resolvent estimates: dissipativity plus
dense range for the closed reflected graph yields the conservative positive
strongly continuous contraction semigroup whose generator is exactly the
graph. Positivity and conservativeness come from the maximum principle for
the interior operator with the oblique boundary condition. -/
theorem oblique_hille_yosida_generation (n : ℕ) (hd : 2 ≤ n + 1)
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
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by sorry
