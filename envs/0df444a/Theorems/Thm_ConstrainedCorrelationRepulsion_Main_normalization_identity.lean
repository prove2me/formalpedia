-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_normalization_identity
-- name    : ConstrainedCorrelationRepulsion.Main.normalization_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:30:03.751687+00:00
-- url     : https://prove2.me/theorems/6ff8ada7-2683-4e06-bc15-c9ef5a8f8a54
-- title:
--   Definition 3.1 — exact normalization and restoration cost identities
-- statement:
--   In the no-must-link regime, let $c_H$ count the original positive hard pairs. Fixed-cost relabelling leaves feasibility unchanged and subtracts $c_H$ from every feasible partition cost. After additionally removing zero-positive-degree vertices, every feasible partition $Q$ of the normalized instance restores to a feasible partition of the original instance, with
--
--   $$
--   \mathrm{cost}_I(\operatorname{restore}Q)-\mathrm{cost}_{\operatorname{normalize}I}(Q)=c_H,\qquad \mathrm{OPT}(I)-\mathrm{OPT}(\operatorname{normalize}I)=c_H.
--   $$
--
--   This auxiliary identity keeps exact restoration costs visible. It is not a milestone or a new numbered source result; only the relabelling step is used after preclustering.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Definition 3.1 and following paragraph, printed p.13 (PDF p.14); retained-vertex distinction printed p.20 (PDF p.21)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Normalization

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem normalization_identity {n : ℕ} (I : Instance n) (hM : I.mustLink = ⊥) :
  (∀ P, Feasible I P ↔ Feasible (relabelOnly I) P) ∧
  (∀ P, Feasible I P →
    (cost I P : ℝ) - (cost (relabelOnly I) P : ℝ) = normalizationCost I) ∧
  (∀ Q, Feasible (normalize I) Q → Feasible I (restore I Q) ∧
    (cost I (restore I Q) : ℝ) - (cost (normalize I) Q : ℝ) = normalizationCost I) ∧
  (OPT I : ℝ) - (OPT (normalize I) : ℝ) = normalizationCost I := by sorry

end ConstrainedCorrelationRepulsion.Main
