-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_5_2
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:29:46.940848+00:00
-- url     : https://prove2.me/theorems/3b23f75e-70ed-4cec-9593-dddbdc151d90
-- title:
--   Lemma 5.2 — full conditioning formulas and positive denominators
-- statement:
--   Let $y$ be one rational optimal bounded-LP table at even level $r\ge6$, let $B(a)$ be the unit of vertex $a$, and let $\mathcal W$ be the other units compatible with it. Every supported size-pivot pair $(s,a)$ has real residual size $t=s-|B(a)|\ge0$. Initial conditional values are $z_T=y_{s,T\cup\{B(a)\}}/y_{s,\{B(a)\}}$, with $z_\varnothing=z_{\{B(a)\}}=1$ and zero on forbidden indices. After each supported seed history, let $S$ be the pivot unit and distinct selected seeds. Denominators are positive, retained entries equal $y_{s,S\cup T}/y_{s,S}$, and whenever $T\subseteq\mathcal W$, $|S\cup T|\le r-1$,
--
--   $$
--   \sum_{D\in\mathcal W}|D|z_{T\cup\{D\}}=t z_T.
--   $$
--
--   The formulas also define analytical entries beyond those retained in storage. Seed histories preserve repeated draws as separate steps; the zero-size case uses the early return, and identity (18) is asserted for the initial table even when $t=0$.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 5.2 with preceding clauses (i)–(ii), printed p.24 (PDF p.25)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_5_2 {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hres : ResidualUnits I U) (hy : BoundedOptimal I U r y) (hq : RationalTable y)
    (s : ℕ) (a : Fin n) (hsa : 0 < y s {unitOf U a}) :
  let t : ℝ := (s : ℝ) - ((unitOf U a).card : ℝ)
  0 ≤ t ∧
  conditionalValue U y s a [] ∅ = 1 ∧ conditionalValue U y s a [] {unitOf U a} = 1 ∧
  (∀ T, T ⊆ U.blocks → (insert (unitOf U a) T).card ≤ r →
    ¬ T ⊆ insert (unitOf U a) (eligible I U a) → conditionalValue U y s a [] T = 0) ∧
  (∀ T, T ⊆ eligible I U a → T.card + 1 ≤ r →
    (initialDraw I U y r s a).table T = conditionalValue U y s a [] T) ∧
  (∀ T, T ⊆ eligible I U a → (insert (unitOf U a) T).card + 1 ≤ r →
    (∑ D ∈ eligible I U a, (D.card : ℝ) * conditionalValue U y s a [] (insert D T)) =
      t * conditionalValue U y s a [] T) ∧
  (0 < t → ∀ j, j ≤ r/2 → ∀ h ∈ (seedSteps I U r (initialDraw I U y r s a) j).support,
    h.seeds.length = j ∧ y s (insert (unitOf U a) h.seeds.toFinset) > 0 ∧
    (∀ T, T ⊆ eligible I U a → T.card + 1 + j ≤ r →
      h.table T = conditionalValue U y s a h.seeds T) ∧
    (∀ T, T ⊆ eligible I U a → (insert (unitOf U a) h.seeds.toFinset ∪ T).card + 1 ≤ r →
      (∑ D ∈ eligible I U a, (D.card : ℝ) * conditionalValue U y s a h.seeds (insert D T)) =
        t * conditionalValue U y s a h.seeds T) ∧
    (j < r/2 → ∀ D ∈ eligible I U a, 0 < h.table {D} →
      0 < y s (insert D (insert (unitOf U a) h.seeds.toFinset)))) := by sorry

end ConstrainedCorrelationRepulsion.Main
