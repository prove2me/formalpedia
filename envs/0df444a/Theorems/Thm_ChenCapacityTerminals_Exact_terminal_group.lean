-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_terminal_group
-- name    : ChenCapacityTerminals.Exact.terminal_group
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:48.238215+00:00
-- url     : https://prove2.me/theorems/8baff0ae-8d79-4790-b1b9-82772bed1103
-- title:
--   Lemma 3.1 — One terminal group enclosure
-- statement:
--   Let $D$ be a valid rooted network with root $q$, nonempty nonroot terminal set $J$, threshold $U>0$, and integer masses at least $1+\deg_D^-(v)$ on nonroots. For every minimizer $B$ over all nonroot subsets, including the empty set, of
--   $$f_D(X)-U|J\cap X|,$$
--   the following assertions hold:
--
--   1. Every $t\in J\setminus B$ has pair minimum-cut value at least $U$.
--   2. Every $t\in J\cap B$ has a minimum pair sink side contained in $B$.
--   3. The enclosure obeys
--   $$f_D(B)\le U|J\cap B|.$$
--   If $D$ is conditioned at a positive rate $\eta$, then also
--   $$b(B)\le\frac U\eta |J\cap B|.$$
--   A single fixed-pair call on the explicitly augmented network finds such an enclosure: every returned optimum shore, with the fresh sink removed, is a minimizer. The statement includes existence of a lawful flow-and-shore oracle, so the call assertion cannot be vacuous.
--
--   This enclosure property preserves exact pair values inside a selected region and certifies excluded labels, for every minimizer tie.
--
--   Differences from the source:
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: a single fixed-pair flow finds B → one evaluation of a lawful flow-and-shore oracle on the explicit augmented network, together with optimal-shore existence and the projection for every optimum; reason: the request is specified independently of its answer and all valid ties are covered
--   - encoding: conditioning at rate η in the bound containing U/η → the rate is explicitly positive in that implication; reason: a positive conditioning rate is the setting of Section 3 and excludes division by zero
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 6, PDF p. 7, Lemma 3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem terminal_group (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ)
    (b : ℕ → ℕ) (hG : G.Valid) (hr : r ∈ G.vertices)
    (hJ : J ⊆ G.vertices \ {r}) (hne : J.Nonempty) (hU : 0 < U)
    (hb : ∀ v ∈ G.vertices \ {r}, 1 + indegree G v ≤ b v) :
    (∀ B, Enclosure G r J U B →
      (∀ t ∈ J \ B, ∀ X, PairSide G r t X → U ≤ cut G X) ∧
      (∀ t ∈ J ∩ B, ∃ X, OptimalPair G r t X ∧ X ⊆ B) ∧
      cut G B ≤ U * (J ∩ B).card ∧
      (∀ η : ℝ, 0 < η → Conditioned G r b η →
        (mass b B : ℝ) ≤ U / η * (J ∩ B).card)) ∧
    (∀ z, z ∉ G.vertices →
      (∃ X, OptimalPair (enclosureNetwork G J U z) r z X) ∧
      ∀ X, OptimalPair (enclosureNetwork G J U z) r z X →
        Enclosure G r J U (X.erase z)) ∧
    (∃ O, LawfulExactOracle O) ∧
    (∀ O, LawfulExactOracle O → ∀ z, z ∉ G.vertices →
      Enclosure G r J U ((O ⟨enclosureNetwork G J U z, r, z⟩).shore.erase z)) := by sorry

end ChenCapacityTerminals.Exact
