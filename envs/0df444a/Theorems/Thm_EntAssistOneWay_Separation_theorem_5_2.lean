-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_5_2
-- name    : EntAssistOneWay.Separation.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:18.574223+00:00
-- url     : https://prove2.me/theorems/e77f1cfb-6c20-4717-842f-0f37248d8f6e
-- title:
--   Theorem 5.2 — unassisted public-coin quantum lower bound
-- statement:
--   There are an absolute $c>0$ and an integer $r_0\ge1$ such that for every $r\ge r_0$, every finite group $G$, and every $D\ge1$ admitting a central element $\zeta$ of order three killed by every representation of dimension less than $D$, any public-coin unassisted quantum protocol for shifted equality with worst-case error at most $1/3$ sends
--   $$C\ge c\min\{2^r,\log_2 D/2^r\}.$$
--   Both $c$ and $r_0$ are chosen before $r,G,D$ and the protocol. The paper writes $\Omega(\cdot)$; the uniform threshold is the sufficiently-large-$r$ reading in its proof. This is a bound on every successful protocol, with no infimum over an empty cost set.
--
--   Differences from the source:
--   - reading: Ω(min(2^r,(log D)/2^r)) → an absolute positive c and a uniform threshold r₀ preceding r,G,D; reason: the proof on pp. 26–27 chooses absolute κ, κ′ and then sufficiently large r
--   - generalization: public coins in finite-input one-way communication → the lower bound holds for every measurable public seed on any probability space; reason: Born probabilities are bounded and measurable, so integrating the distributional lower bound covers every such seed, including the source coins
--   - encoding: finite-dimensional coordinate Hilbert spaces and C-bit or C-qubit messages → Fin d matrix indices and message indices Fin (2^C); reason: these label every coordinate and every length-C message without restricting states or measurements
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 25, Theorem 5.2; pp. 26–27, asymptotic proof

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems
import Definitions.Def_EntAssistOneWay_Separation_Probability

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 5.2, p. 25, with a uniform asymptotic threshold in r. -/
theorem theorem_5_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, 1 ≤ r₀ ∧
      ∀ r : ℕ, r₀ ≤ r → ∀ (G : Type) [Group G] [Fintype G]
        (D : ℕ), (∃ ζ : G, CentralThree ζ ∧ DimensionGap ζ D) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (C : ℕ)
          (P : QuantumProtocol (ShiftAlice G r) (ShiftBob G r) Ω C),
          ComputesWithError (shiftEq r) (randomizedQuantumAccept P) (1 / 3) →
          c * min ((2 : ℝ) ^ r) (log₂ D / (2 : ℝ) ^ r) ≤ (C : ℝ) := by sorry

end

end EntAssistOneWay.Separation
