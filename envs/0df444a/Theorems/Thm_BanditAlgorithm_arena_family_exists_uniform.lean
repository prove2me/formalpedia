-- Prove2me | Theorems.Thm_BanditAlgorithm_arena_family_exists_uniform
-- name    : BanditAlgorithm.arena_family_exists_uniform
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T23:10:47.486058+00:00
-- url     : https://prove2.me/theorems/77f1c33c-7049-48be-853f-9c515716d1cf
-- title:
--   Existence of the hard arena family, with diameter $\le 4(\delta^{-1}+d+1)$ uniformly in $(\delta,\Delta)$
-- statement:
--   **The construction step of the $\Omega(\sqrt{DSAn})$ MDP lower bound.**
--
--   For every $S \ge 3$ and $A \ge 2$ there is a layered arena $E_0$ on $S$ states and $A$ actions, together with a family $(E_p)$ of arenas indexed by the leaf--action pairs of $E_0$, with the following properties.
--
--   1. **All members share the same skeleton.** The rewarding state $s_g$, the unrewarding state $s_b$, the root, the level function, the depth and the child map of $E_p$ agree with those of $E_0$ for every $p$; the members differ *only* in where the advantage is planted, and member $E_p$ plants it exactly at $p$. Two members therefore differ in a single transition row, which is what makes the family amenable to a change-of-measure argument.
--
--   2. **The family is large.** With $L \ge 1$ the number of leaves, the index set has exactly $LA$ members and $S - 2 \le 3L + 1$, so $L = \Theta(S)$ and the family has $\Theta(SA)$ members. This is the source of the factor $\sqrt{SA}$ in the final rate.
--
--   3. **The tree is shallow:** $A^{d} < A(S-2)$ for the common leaf depth $d$, that is, $d \le 1 + \log_A(S-2)$.
--
--   4. **Every member has small diameter, uniformly in the parameters.** For *every* choice of restart probability $\delta \in (0,1]$ and advantage $\Delta \le 1/4$, and every $p$, the MDP induced by $E_p$ has diameter at most $4(\delta^{-1} + d + 1)$ — four expected episode lengths. Travel to a tree node by routing down the path from the root; travel to $s_g$ or $s_b$ by descending and gambling, which succeeds with probability at least $1/4$ per attempt. The bound is stated uniformly in $(\delta,\Delta)$ because the tuning of those parameters depends on the depth $d$ and the leaf count $L$, which are outputs of this construction.
--
--   All leaves sit at the *same* depth $d$, a deliberate strengthening of the book, which takes a tree of minimum depth. With leaves at two depths an episode through a shallow leaf is one round shorter, worth $\approx\delta/2$ of gain, while the planted advantage is only $\Delta = \Theta(\sqrt{kD/n})$; for large $n$ the optimal gain would then be attained at a leaf carrying *no* advantage, and the regret decomposition of Claim 38.11 would fail.
-- source:
--   ORIGIN: Thomas Jaksch, Ronald Ortner, Peter Auer, 'Near-optimal Regret Bounds for Reinforcement Learning', JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1567) and its proof in Section 6 'The Lower Bound', pp. 1582-1586. JAO prove: for S, A >= 10, D >= 20 log_A S and T >= DSA there is an MDP with S states, A actions and diameter D forcing expected regret >= 0.015 sqrt(DSAT). EXPOSITION FOLLOWED HERE: Lattimore-Szepesvari, Bandit Algorithms, Cambridge 2020, Theorem 38.7 (p. 529) and Section 38.7 (pp. 529-534), which restates the result for S >= 3, A >= 2, D >= 6 + 2 log_A S. DEVIATION: L&S build 'a tree of minimum depth' (p. 529); this node instead places every leaf at the SAME depth. With leaves at two depths an episode through a shallow leaf is one round shorter, worth about delta/2 of gain, while the planted advantage is only Delta = Theta(sqrt(kD/n)), so for large n the optimal gain is attained at a leaf carrying no advantage and L&S Claim 38.11 fails. JAO avoid this because their tree only connects the s-circle states and is collapsed in the analysis. This node supplies the construction and the diameter bound (JAO Section 6, the composite MDP of Figure 4 and the bound 2(D/4 + ceil(log_{A'} k)); L&S Fig. 38.3).

import Definitions.Def_LayeredArena

open MeasureTheory ProbabilityTheory
open scoped NNReal
open BanditAlgorithm BanditAlgorithm.LayeredArena

theorem BanditAlgorithm.arena_family_exists_uniform
    {S A : ℕ} [NeZero S] (hS : 3 ≤ S) (hA : 2 ≤ A) :
    ∃ (E₀ : LayeredArena S A)
      (Efam : ↥(countedPairs E₀.leafNat) → LayeredArena S A) (L : ℕ),
      (∀ p, E₀.good = (Efam p).good) ∧ (∀ p, E₀.bad = (Efam p).bad) ∧
      (∀ p, E₀.root = (Efam p).root) ∧ (∀ p, E₀.lvl = (Efam p).lvl) ∧
      (∀ p, E₀.depth = (Efam p).depth) ∧ (∀ p, E₀.child = (Efam p).child) ∧
      (∀ p, (Efam p).specialLeaf = p.val.1) ∧
      (∀ p, (Efam p).specialAction = p.val.2) ∧
      Fintype.card ↥(countedPairs (A := A) E₀.leafNat) = L * A ∧ 1 ≤ L ∧
      A ^ E₀.depth < A * (S - 2) ∧ S - 2 ≤ 3 * L + 1 ∧
      ∀ (δ Δ : ℝ≥0) (hδ1 : δ ≤ 1) (hΔ2 : Δ ≤ 1 / 2), (0 : ℝ) < δ → Δ ≤ 1 / 4 →
        ∀ p, mdpDiameterENN ((Efam p).toMDP hδ1 hΔ2)
          ≤ ENNReal.ofReal (4 * E₀.epiLen (δ : ℝ)) := by
  sorry
