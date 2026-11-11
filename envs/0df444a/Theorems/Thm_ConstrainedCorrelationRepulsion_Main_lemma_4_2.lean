-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_4_2
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:46.841264+00:00
-- url     : https://prove2.me/theorems/a5f125ce-e7a2-4a4f-8d02-33faa85b9913
-- title:
--   Lemma 4.2 — polynomial atom construction and the free-degree budget
-- statement:
--   A deterministic polynomial-time algorithm constructs disjoint atoms, singleton free units, and the free vertex set $F$ for an unweighted cannot-link instance $I$. Each selected non-singleton is preserved by every optimum, and
--
--   $$
--   \sum_{v\in F}e^+(v,V)\le60006\,\mathrm{OPT}(I).
--   $$
--
--   The degree sum includes all trimming losses, including the vertices made free while obtaining the 2-expansion certificate.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - encoding: an absolute constant Cpre → the common value Cpre = 60006; reason: the proof supplies 6 times 10001 on printed p.20 (PDF p.21)
--   - generalization: the normalized instance entering preclustering → an arbitrary unweighted cannot-link instance; reason: the construction and its degree estimate work before normalization as well; isolated vertices contribute zero
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 4.2, printed p.19 (PDF p.20), proof printed pp.19–20 (PDF pp.20–21)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_4_2 :
  ∃ code : Program, Deterministic code ∧ ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n), FeasibleInput I → I.mustLink = ⊥ →
      let B := polynomialBound C d n
      BoundedRun true code (inputOracle I) (initialState n) B ∧
      ∀ s ∈ (machineRun true code (inputOracle I) (initialState n) B).support,
        ∃ U : Units n,
          (∀ u v, s.natMem u.val = s.natMem v.val ↔ unitOf U u = unitOf U v) ∧
          (∀ A ∈ atoms U, IsAtom I A) ∧ freeDegree I U ≤ Cpre * OPT I := by sorry

end ConstrainedCorrelationRepulsion.Main
