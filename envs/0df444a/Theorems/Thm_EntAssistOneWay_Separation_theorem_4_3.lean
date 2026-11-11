-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_4_3
-- name    : EntAssistOneWay.Separation.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:43.656213+00:00
-- url     : https://prove2.me/theorems/c4da77fc-6520-4e96-a315-1afec619408d
-- title:
--   Theorem 4.3 — reverse one-way and SMP classical protocols
-- statement:
--   For every finite group $G$ and $1\le k\le|G|$, bounded-order subgroup membership has both a public-coin Bob-to-Alice protocol and an SMP protocol with randomness shared only by Alice and Bob, each with worst-case error at most $1/3$. The exact message budgets provided by the proof are
--   $$C_{B\to A}=\lceil\log_2(3k)\rceil,\qquad c_A=3k,\quad c_B=\lceil\log_2(3k)\rceil.$$
--   One absolute $c>0$, chosen before $G,k$, bounds the first cost by $c\log_2k$ for $k\ge2$ and the SMP total by $ck$ for $k\ge1$. The paper writes $O(\log k)$ and $O(k)$. The reverse one-way protocol also supplies the stated two-way bound. The SMP clause yields the matching unassisted upper bound in the final separation.
--
--   Differences from the source:
--   - generalization: an O(log k) two-way protocol and an O(k) SMP protocol → a Bob-to-Alice one-way protocol and the exact message budgets displayed above; reason: these are the protocols and costs explicitly given on p. 24, so they imply both source bounds
--   - reading: O(log k) for 1 ≤ k ≤ |G| → the logarithmic multiplicative inequality holds for k ≥ 2, with an explicit protocol also at k = 1; reason: log 1 is zero whereas the reverse-direction protocol can need communication; asymptotic O does not impose a zero cost at k = 1
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 20, Theorem 4.3; pp. 23–24, proof

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems
import Definitions.Def_EntAssistOneWay_Separation_SMPProtocol

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 4.3, pp. 20, 24: the first protocol is Bob-to-Alice. -/
theorem theorem_4_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Type) [Group G] [Fintype G]
      (k : ℕ), 1 ≤ k → k ≤ Fintype.card G →
      (∃ P : ClassicalProtocol G (SmallSubgroup G k) (logCeil (3 * k)),
        ComputesWithError (fun g H => membership G k H g) (classicalAccept P) (1 / 3) ∧
        (2 ≤ k → (logCeil (3 * k) : ℝ) ≤ c * log₂ k)) ∧
      (∃ P : SMPProtocol (SmallSubgroup G k) G (3 * k) (logCeil (3 * k)),
        ComputesWithError (membership G k) (smpAccept P) (1 / 3) ∧
        ((3 * k + logCeil (3 * k) : ℕ) : ℝ) ≤ c * k) := by sorry

end

end EntAssistOneWay.Separation
