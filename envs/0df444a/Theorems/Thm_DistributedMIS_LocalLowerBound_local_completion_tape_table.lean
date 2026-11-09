-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_local_completion_tape_table
-- name    : DistributedMIS.LocalLowerBound.local_completion_tape_table
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:35.158573+00:00
-- url     : https://prove2.me/theorems/eb9b2ed5-475b-4785-ad68-6248bac0eda3
-- title:
--   Lemma A.3 — Local completion and the tape table
-- statement:
--   Fix a clique v in the finite construction. For each matrix realization there exists a legal identifier assignment I to the padded n-vertex graph, chosen before the tape table, such that on the event of distinct tentative IDs in B^H_{T+2}(v), I preserves those IDs and for every tape table the repaired execution at v equals the repaired tentative-ID simulation.
--
--   $$\mathcal L\bigl((W_{I(x)})_x\mid\text{matrices}\bigr)
--   =\bigotimes_x\operatorname{Bernoulli}(1/2)^{\otimes\mathbb N}.$$
--
--   The law is stated as an equality of actual product measures. This restores a legal input without changing the algorithm's private-tape law.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - encoding: arbitrary synchronous LOCAL computation and unbounded messages with independent infinite private tapes → one uniform full-state initialization, transition and output program, with total executions; reason: a state can store the original state, tape, round and port table, so every per-port message can be reconstructed from the full-state broadcast; programs may be chosen separately for each n and may idle until T
--   - generalization: the large occupancy threshold and unhinted simulation → D≥3 and any fixed advice value; reason: local completion and permutation of the independent table do not require the occupancy bound or any special value of a fixed uniform input
--   - generalization: a randomized LOCAL algorithm with the usual measurable execution convention → any total LocalProgram, without a MeasurableProgram hypothesis; reason: the execution agreement is pointwise for every tape table, and the asserted product-measure permutation depends only on the identifier bijection, not on the program
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.3, printed/PDF pp. 33

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem local_completion_tape_table (n D k N T advice : ℕ) (hn : 1 ≤ n)
    (H : SimpleGraph (Fin N)) (hH : finiteParameters n D k N T 3 H)
    (P : LocalProgram) (v : Fin N) :
    ∀ ω : Matrices k, ∃ I : PaddedVertices n N k ≃ Fin n,
      (distinctIDs n (T+2) (finiteNeighbors H) Fin.val ω v →
        (∀ w : Fin N, w ∈ networkBall (finiteNeighbors H) (T+2) v → ∀ a : Fin k,
          (I (Sum.inl (w,a))).val + 1 = tentativeID n (finiteNeighbors H) Fin.val ω w a) ∧
        (∀ W : Fin n → PrivateTape, ∀ a : Fin k,
          repaired P n advice T W (finiteNeighbors H) Fin.val ω (v,a) =
          legalRepaired P advice T H ω I W (Sum.inl (v,a)))) ∧
      (privateTapes n).map (fun W x => W (I x)) =
        MeasureTheory.Measure.pi (fun _ : PaddedVertices n N k => tapeMeasure) := by sorry

end DistributedMIS.LocalLowerBound
