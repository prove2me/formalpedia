-- Prove2me | Theorems.Thm_EthierKurtz_oblique_holder_resolvent
-- name    : EthierKurtz.oblique_holder_resolvent
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T03:02:28.882556+00:00
-- url     : https://prove2.me/theorems/a32caa6f-7410-44a3-89ed-a03d46950585
-- title:
--   Exact resolvent solvability for Hölder data
-- statement:
--   Exact resolvent solvability for Hölder data.
--
--   Under the hypotheses of Theorem 1.5 (bounded connected $C^{2,\mu}$ region, uniformly elliptic operator with Hölder coefficients, uniformly oblique $C^{1,\mu}$ reflection field), there is a rate $\lambda_0 > 0$ such that every Hölder right-hand side is hit exactly by the resolvent map of the reflected graph $A$:
--
--   $$
--   \forall h \text{ Hölder},\ \exists (f, g) \in A,\quad \lambda_0 f - g = h.
--   $$
--
--   This is the elliptic-existence core: the oblique-derivative Schauder theory for the interior equation produces a classical solution whose pair lies in the graph. Lipschitz data is Hölder (since $\mu \le 1$), hence admissible — that embedding is a separate obligation.
--
--   **Formalization Note** Lean quantifies $h$ over bounded continuous functions on $closure~\Omega$ satisfying `HolderWith` with exponent $\mu$, and the graph pair lies in the un-closed reflected graph (classical solutions); passing to the closure is a one-line weakening.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); Hölder-data existence step via the oblique-derivative elliptic theory for (1.15).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Exact resolvent solvability for Holder data: for some positive rate,
every Holder right-hand side is hit exactly by the resolvent map on the
reflected graph, via the oblique-derivative elliptic existence theory for
the interior equation (1.15) (Schauder theory). This is the PDE core
behind Lipschitz solvability; Lipschitz data is Holder, hence admissible. -/
theorem oblique_holder_resolvent (n : ℕ) (hd : 2 ≤ n + 1)
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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c,
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
