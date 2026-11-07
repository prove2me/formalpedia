-- Prove2me | Theorems.Thm_CFLOutliers_lemma_4_1
-- name    : CFLOutliers.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:58.589843+00:00
-- url     : https://prove2.me/theorems/d7e8ed7a-a2d6-4d80-abe3-032f684fc2f1
-- title:
--   Lemma 4.1 — a bounded family of open and averaged close comparisons
-- statement:
--   Let transport data be given: sources and real targets with a pseudometric $c$, $\lambda\ge 0$, loads $w_s$, an integral transport $y_{st}$ and disposal quantities $z_s$ with $\sum_t y_{st}+z_s=w_s$, column sums $Q_t=\sum_s y_{st}\le\hat u(t)$ and $\hat u(t)\ge 1$, and $\alpha=\sum_{s,t}y_{st}c_{st}+\lambda\sum_s z_s$. Then there is a finite family of open and averaged close comparisons with weights in $(0,1]$ such that
--
--   1. every source is closed with total weight one;
--   2. every real target appears in at most five comparisons;
--   3. every real target $t$ receives total weighted quantity at most $2Q_t$ ($\le 2\hat u(t)$);
--   4. the total weighted transfer and rejection charge is at most $2\alpha$;
--   5. the total weight of the comparisons is at most the number of sources (at most $m$).
--
--   Summing the open inequality (16) and the averaged close inequality (17) over this family, with the add inequalities (15) as padding, gives the facility-cost bound (19) behind Theorem 2.1.
--
--   Differences from the source:
--   - generalization: the cycle-free transport of §4.3 (a forest) built from the assignment-path decomposition of a terminal solution and an optimum → any finite sets of sources and targets with a pseudometric and any integral transport y, disposal z, loads w and capacities û with Σ_t y_st + z_s = w_s, Q_t ≤ û(t), û(t) ≥ 1, λ ≥ 0; reason: §4.3 cancels cycles by integral adjustments that keep the row sums, the column sums Q_t and the z_s and do not increase α, so the forest case implies the general one; the lemma uses only these relations
--   - generalization: total primitive weight at most m (the number of facilities) → total weight at most the number of sources; reason: the sources S = F_S \ F_O are facilities, so their number is at most m
--   - reading: "a family of open and averaged close comparisons … with total weight one … appears in at most five comparisons … total weight of the primitive … comparisons" → a finite list of (weight ∈ (0,1], comparison) pairs; appearances count list entries; quantities, charges and weights are weighted sums over the list, an averaged close counting with its own weight; reason: the paper leaves the representation of the family implicit; an averaged close is a convex combination of primitive closes of total weight equal to its weight (Appendix C.1)
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Lemma 4.1, p.12; §4.3, p.11; Appendix C.2, pp.15–17

import Mathlib
import Definitions.Def_CFLOutliers_Transport

namespace CFLOutliers

open Finset

/-- **Lemma 4.1** (Dabas, arXiv:2611.04094, p.12; proof in Appendix C, pp.15–17).
For valid transport data there is a finite family of open and averaged close comparisons, with
weights in `(0, 1]`, such that
1. every source is closed with total weight one;
2. every real target appears in at most five comparisons;
3. every real target receives total (weighted) quantity at most `2 Q_t`;
4. the total (weighted) transfer and rejection charge is at most `2 α`;
5. the total weight is at most the number of sources.

**Formalization Note.** The family is a finite list of (weight, comparison) pairs; "appears in at
most five comparisons" counts list entries. The transport `y` is any integral transport with the
row sums, column sums and disposal quantities of §4.1 (the cycle-free forest of §4.3 is obtained
inside the proof by cycle cancelling, which keeps these and does not increase `α`). The bound `m`
of the paper is taken as `|Src|`, the number of sources, which is at most the number of
facilities. -/
theorem lemma_4_1 {Src Tgt : Type} [Fintype Src] [Fintype Tgt] (D : Transport Src Tgt)
    (hD : D.Valid) :
    ∃ fam : List (ℝ × Comparison Src Tgt),
      (∀ p ∈ fam, 0 < p.1 ∧ p.1 ≤ 1 ∧ Comparison.Admissible D p.2) ∧
      (∀ s, closedWeight fam s = 1) ∧
      (∀ t, appearCount fam t ≤ 5) ∧
      (∀ t, (fam.map (fun p => p.1 * (Comparison.quantity D p.2 t : ℝ))).sum ≤ 2 * (D.Q t : ℝ)) ∧
      (fam.map (fun p => p.1 * Comparison.charge D p.2)).sum ≤ 2 * D.alpha ∧
      (fam.map (fun p => p.1)).sum ≤ (Fintype.card Src : ℝ) := by sorry

end CFLOutliers
