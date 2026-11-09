-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_fact_1
-- name    : DetStreamClique.MaxClique.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:07:36.495667+00:00
-- url     : https://prove2.me/theorems/affff73f-4cbb-4884-b30e-42c3d4ff9951
-- title:
--   Fact 1 — streaming space bounds one-way communication
-- statement:
--   Fix $\beta\ge1$ and an $n$-vertex deterministic streaming machine with memory alphabet $S$ encodable in $s$ bits, correct on every insertion-only edge stream. There exists a deterministic one-way protocol for the same clique approximation problem whose message alphabet is exactly $S$, with
--   $$\operatorname{CC}(\pi)\le s.$$
--   Bob's output is a clique of size at least $\omega(E_A\cup E_B)/\beta$ for every edge-disjoint pair of inputs. This is the communication-to-streaming interface used by the goal.
--
--   Differences from the source:
--   - encoding: an n-vertex graph and its edge-arrival streams → vertices Fin n; distinct non-loop unordered edge lists; finite states with card ≤ 2^s; reason: these represent every simple graph, every insertion order and every memory state; real division is used for approximation
--   - generalization: algorithms in the insertion-deletion streaming setting → correctness is required only on insertion-only streams; reason: every insertion-deletion algorithm restricts to such a machine with the same memory; the paper proof uses insertions only
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Fact 1, p. 6

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Graphs

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Fact 1, p. 6, specialized to the problem used by Theorem 1.1. -/
theorem fact_1 {n : ℕ} {S : Type} [Fintype S]
    (a : StreamingMachine (Edge n) (Finset (Fin n)) S)
    (β : ℝ) (hβ : 1 ≤ β) (s : ℕ) (hbits : FitsBits S s)
    (hcorrect : StreamCorrect a β) :
    ∃ π : OneWayProtocol (Graph n) (Graph n) S (Finset (Fin n)),
      ProtocolCorrect π β ∧ FitsBits S s := by sorry

end DetStreamClique.MaxClique
