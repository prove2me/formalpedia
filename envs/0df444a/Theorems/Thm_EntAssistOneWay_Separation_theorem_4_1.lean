-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_4_1
-- name    : EntAssistOneWay.Separation.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:39.043722+00:00
-- url     : https://prove2.me/theorems/3eaace1c-0e85-4ac6-b07f-6491b84b1fce
-- title:
--   Theorem 4.1 — entanglement-assisted subgroup membership
-- statement:
--   There is an absolute constant $c>0$ such that for every finite group $G$ and every $1\le k\le|G|$, bounded-order subgroup membership has a one-way classical protocol with worst-case error at most $1/3$, using
--   $$E=2\lceil\log_2|G|\rceil\quad\text{EPR pairs},\qquad C\le c\log_2k\quad\text{bits}.$$
--   The EPR count is exact. For $k=1$ the inequality forces $C=0$, as Bob can test membership in the identity subgroup directly. This upper bound is uniform over all finite groups and is used after the reduction from shifted equality. The paper writes $O(\log k)$; $c$ is quantified before $G,k$.
--
--   Differences from the source:
--   - encoding: finite-dimensional coordinate Hilbert spaces and C-bit or C-qubit messages → Fin d matrix indices and message indices Fin (2^C); reason: these label every coordinate and every length-C message without restricting states or measurements
--   - encoding: uses exactly 2⌈log₂|G|⌉ shared EPR pairs → fixed EPR state with no additional public seed; reason: the resource count is part of the theorem, and local randomness is already contained in the measurements
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 20, Theorem 4.1; pp. 21–22, proof

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_Probability
import Definitions.Def_EntAssistOneWay_Separation_EAProtocol
import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 4.1, p. 20; the exact shared-entanglement count is included. -/
theorem theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Type) [Group G] [Fintype G]
      (k : ℕ), 1 ≤ k → k ≤ Fintype.card G →
      ∃ (C : ℕ) (P : EAProtocol (SmallSubgroup G k) G (2 * logCeil (Fintype.card G)) C),
        (C : ℝ) ≤ c * log₂ k ∧
        ComputesWithError (membership G k) (eaAccept P) (1 / 3) := by sorry

end

end EntAssistOneWay.Separation
