-- Prove2me | Theorems.Thm_EthierKurtz_oblique_dense_range
-- name    : EthierKurtz.oblique_dense_range
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T04:32:50.8326+00:00
-- url     : https://prove2.me/theorems/50abf88b-70c7-4165-8bf7-c67b788877b1
-- title:
--   Dense range of the reflected resolvent
-- statement:
--   Dense range of the reflected resolvent.
--
--   Under the hypotheses of Theorem 1.5 (bounded connected $C^{2,\mu}$ region,
--   uniformly elliptic operator with H\"older coefficients, uniformly oblique
--   $C^{1,\mu}$ reflection field), there is a rate $\lambda_0 > 0$ such that the
--   image of the closed reflected graph $A$ under the resolvent map
--   $(f, g) \mapsto \lambda_0 f - g$ is dense in $C(\bar\Omega)$: every
--   continuous target is uniformly approximable,
--
--   $$
--   \forall h,\ \forall \delta > 0,\ \exists (f, g) \in A,\quad
--   \lVert (\lambda_0 f - g) - h\rVert < \delta.
--   $$
--
--   This is the elliptic-existence half of the Hille--Yosida argument, proved by
--   solving the oblique-derivative boundary value problem for the interior
--   equation (1.15) with right-hand side $h$.
--
--   **Formalization Note** Lean quantifies $h$ over bounded continuous functions
--   on $closure~\Omega$ with $A := closure~(obliqueDiffusionGraph~\Omega~\mu~a~b~c)$.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); resolvent equation for the operator (1.15).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Dense range of the reflected resolvent: for some positive rate, the
image of the closed graph (1.20) under the resolvent map is dense in the
continuous functions on the closed region, via solvability of the
oblique-derivative elliptic problem for the interior equation (1.15). -/
theorem oblique_dense_range (n : ℕ) (hd : 2 ≤ n + 1)
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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by sorry
