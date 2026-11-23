-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_enclosure_properties
-- name    : ChenCapacityTerminals.Exact.enclosure_properties
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:34.251321+00:00
-- url     : https://prove2.me/theorems/87855ee0-13ce-4769-88e0-7a1179c8a281
-- title:
--   Lemma 3.1 — submodular enclosure inequalities and contained minimum shores
-- statement:
--   Let $D$ be a valid directed network with root $q$, a terminal set $J$ contained in its nonroots, and $U>0$. Suppose $B$ minimizes $f_D(X)-U|J\cap X|$ over all nonroot subsets $X$. Then every terminal $t\in J\setminus B$ has every $q$-to-$t$ sink side of capacity at least $U$; every $t\in J\cap B$ has a minimum sink side contained in $B$; and
--   $$f_D(B)\le U|J\cap B|.$$
--   Consequently, for every $\eta>0$ for which $D$ is conditioned with respect to $b$, the enclosure has mass
--   $$b(B)\le \frac U\eta|J\cap B|.$$
--
--   This is the submodular part of Lemma 3.1. It mirrors the paper’s comparison with $B\cup S$ and $S\cap B$, and is stated independently of how a minimizer is constructed.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Lemma 3.1 (1)–(3), p. 6, PDF p. 7 and its proof continuing on PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.enclosure_properties (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ)
    (b : ℕ → ℕ) (hG : G.Valid) (hJ : J ⊆ G.vertices \ {r}) (hU : 0 < U)
    (B : Finset ℕ) (hB : Enclosure G r J U B) :
    (∀ t ∈ J \ B, ∀ X, PairSide G r t X → U ≤ cut G X) ∧
    (∀ t ∈ J ∩ B, ∃ X, OptimalPair G r t X ∧ X ⊆ B) ∧
    cut G B ≤ U * (J ∩ B).card ∧
    (∀ η : ℝ, 0 < η → Conditioned G r b η →
      (mass b B : ℝ) ≤ U / η * (J ∩ B).card) := by sorry
