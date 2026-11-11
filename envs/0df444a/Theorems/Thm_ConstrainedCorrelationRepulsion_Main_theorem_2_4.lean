-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_2_4
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:45.120908+00:00
-- url     : https://prove2.me/theorems/a9420b3e-52c6-4096-a0af-eeb68c0ab341
-- title:
--   Theorem 2.4 — lossless preclustering with exact fixed-cost restoration
-- statement:
--   The Figure 4 construction has a deterministic polynomial-time implementation on every feasible unweighted cannot-link instance $I$. It returns units and a residual instance $I'$ on the same vertex set. Hard pairs are absent within units and are complete cross-products between incompatible units. Every compatible pair of distinct units has a free endpoint. Every optimum of $I'$ preserves each atom and separates distinct atoms. Also $\mathrm{OPT}(I')\le\mathrm{OPT}(I)$ and the free positive-degree sums with both the original and residual labels are at most $60006\,\mathrm{OPT}(I)$. Every optimum of $I$ remains feasible for $I'$ and preserves the units. For every feasible unit-preserving partition $P$ of $I'$,
--
--   $$
--   \mathrm{cost}_I(P)-\mathrm{cost}_{I'}(P)=\mathrm{OPT}(I)-\mathrm{OPT}(I').
--   $$
--
--   Such a partition is feasible for $I$. The trace specifies the construction separately from these guarantees; the final normalization relabels forced positive hard pairs and retains all units and vertices.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - encoding: an absolute constant Cpre → the common value Cpre = 60006; reason: the proof supplies 6 times 10001 on printed p.20 (PDF p.21)
--   - generalization: the normalized input stipulated at the opening of Section 4 → any feasible unweighted instance with only cannot-links; reason: the metric rounding, trimming, witness and degree arguments apply before normalization too; no step uses positive degrees or negative labels on hard pairs
--   - encoding: the free-degree budget with labels before the final relabelling → the original-label budget and its residual-label consequence; reason: printed p.21 proves the original-label bound; relabelling only removes positive edges, so the same bound also holds afterwards
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 2.4, printed pp.20–21 (PDF pp.21–22)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_2_4 :
  ∃ code : Program, Deterministic code ∧ ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n), FeasibleInput I → I.mustLink = ⊥ →
      let B := polynomialBound C d n
      BoundedRun true code (inputOracle I) (initialState n) B ∧
      ∀ s ∈ (machineRun true code (inputOracle I) (initialState n) B).support,
        ∃ (J : Instance n) (U : Units n), EncodesPrecluster s J U ∧
          PreclusterTrace I J U ∧ PreclusterGuarantees I J U := by sorry

end ConstrainedCorrelationRepulsion.Main
