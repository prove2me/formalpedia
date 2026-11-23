-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_optimal_augmented_projection
-- name    : ChenCapacityTerminals.Exact.optimal_augmented_projection
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:04:03.60126+00:00
-- url     : https://prove2.me/theorems/443fc7f1-e24d-4b79-95a4-4155fd37752b
-- title:
--   Lemma 3.1 — an augmented optimum projects to an enclosure
-- statement:
--   Let $D$ be valid, let $J$ consist of nonroot terminals, and let $z$ be fresh. If $X$ is any minimum $q$-to-$z$ sink side in the network obtained by adding arcs $t\to z$ of capacity $U$ for every $t\in J$, then $X\setminus\{z\}$ minimizes
--   $$f_D(B)-U|J\cap B|$$
--   among nonroot subsets. The assertion covers every optimal tie.
--
--   Indeed, the augmented cut value of any such optimum is its original objective plus the constant $U|J|$; inserting $z$ into every comparison side gives the same identity. Freshness ensures that deleting $z$ does not change the original entering capacity.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Lemma 3.1 proof, p. 6, PDF p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.optimal_augmented_projection (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ) (z : ℕ)
    (hG : G.Valid) (hr : r ∈ G.vertices) (hJ : J ⊆ G.vertices \ {r}) (hz : z ∉ G.vertices)
    (X : Finset ℕ) (hX : OptimalPair (enclosureNetwork G J U z) r z X) :
    Enclosure G r J U (X.erase z) := by sorry
