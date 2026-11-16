-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_Supplement_theorem_4_2
-- name    : EntAssistOneWay.Separation.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:51:41.599211+00:00
-- url     : https://prove2.me/theorems/874e9c7e-a8ce-4a37-8ca8-574ef16dc187
-- title:
--   Theorem 4.2 — public-coin one-way protocol for abelian subgroup membership
-- statement:
--   There is an absolute constant $c>0$ such that for every finite abelian group $G$ and every $1\le k\le|G|$, the bounded-order subgroup membership function $\mathrm{Memb}_{G,k}$ (Alice holds a subgroup $H\le G$ with $|H|\le k$, Bob holds $g\in G$, the answer is $[g\in H]$) has a one-way public-coin randomized protocol from Alice to Bob with worst-case error at most $1/3$ using $C$ bits, where
--
--   $$C\le c\log_2 k.$$
--
--   That is, $C^{1,\mathrm{pub}}_{1/3}(\mathrm{Memb}_{G,k})=O(\log k)$. For abelian groups the entanglement-assisted upper bound of Theorem 4.1 is matched without entanglement, so bounded-order subgroup membership cannot give a quantum–classical separation on an abelian group.
--
--   **Formalization Note** The paper writes $O(\log k)$; $c$ is quantified before $G$ and $k$. At $k=1$ the bound forces $C=0$, which holds since $H=\{1\}$.
--
--   Differences from the source:
--   - encoding: O(log k) → ∃ c > 0 before G and k with C ≤ c·log₂ k; reason: an absolute constant, uniform over all finite abelian groups and k
--   - encoding: one-way public-coin randomized protocol (public and private coins) → published ClassicalProtocol: a probability law on deterministic one-way tables (SmallSubgroup G k → Fin (2^C), G → Fin (2^C) → Bool); reason: every public/private-coin one-way protocol is such a law; same instances
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 20, Theorem 4.2; pp. 22–23, proof

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_Probability
import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
open EntAssistOneWay.Separation
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- Theorem 4.2, p. 20: for finite abelian groups, bounded-order subgroup membership has a
one-way (Alice → Bob) public-coin randomized protocol with `O(log k)` bits and error `1/3`. -/
theorem theorem_4_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Type) [CommGroup G] [Fintype G]
      (k : ℕ), 1 ≤ k → k ≤ Fintype.card G →
      ∃ (C : ℕ) (P : ClassicalProtocol (SmallSubgroup G k) G C),
        (C : ℝ) ≤ c * log₂ k ∧
        ComputesWithError (membership G k) (classicalAccept P) (1 / 3) := by sorry

end

end EntAssistOneWay.Separation.Supplement
