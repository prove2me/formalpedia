-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_lemma_3_2
-- name    : CatalanHashing.Dynamic.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:07.999464+00:00
-- url     : https://prove2.me/theorems/d19b069c-1dbc-4b41-9cbb-409c19a4d8ab
-- title:
--   Lemma 3.2 — if every stored item has expected positive-query scan cost at most C|x|, a negative query has expected scan cost at most 1 + C
-- statement:
--   Consider a static Catalan table on $m$ cells whose items $x\in S$ (with $|x|\ge1$) have random canonical cells $c(x)$ and are placed by an arbitrary, possibly randomised, rule, giving a Catalan placement on every outcome. Let $L_x$ be the scan cost of the query procedure for $x$, and let $C\ge0$ satisfy
--   $$\mathbb E[L_x]\le C|x|\qquad\text{for every }x\in S.$$
--   Let $y$ be a key not in the table whose canonical cell is uniform on the $m$ cells and independent of the table. Then the scan cost $D$ of the negative query for $y$ satisfies
--   $$\mathbb E[D]\le 1+C.$$
--   This reduces negative queries to positive ones for every static construction of the paper; with Theorem 1.3 it gives the $1+1/\varepsilon$ negative-query bound of ARCH.
--
--   Differences from the source:
--
--   - reading: "a static implementation of Catalan hashing using an arbitrary placement rule" → random canonical cells cS and a random occupancy occ on a probability space (Ω, P), with IsCatalanPlacement on every outcome (placement, nesting, every item at or after its canonical cell inside its run); any joint law; reason: the placements of a static Catalan table are those to which the query procedure of Section 3 applies; the rule and its randomness are otherwise arbitrary
--   - reading: the scan cost of the query procedure of Section 3 (Catalan parser with home and stop bits) → queryCost: the number of cells from c(k) through the first cell that is empty, is the last cell of the sought item, or is the last cell of another item with canonical cell c(k) carrying the stop bit (1 if c(k) is not a home cell); reason: these are the stopping rules of Section 3, evaluated on the placement; that the parser recognises them is Lemma A.1
--   - encoding: y not in the table, c(y) uniform and independent of the randomness that places S → expectation over P ⊗ (uniform on Fin m), the second coordinate being c(y); reason: the product measure is exactly independence plus uniformity
--   - reading: "Let C be a parameter" → 0 ≤ C; reason: for C < 0 and S = ∅ the conclusion E[D] = 1 ≤ 1 + C fails; C ≥ 0 is implicit in a bound E[L_x] ≤ C|x| on a positive cost
--   - encoding: expectations E[·] → lintegrals of ℕ-valued costs in ℝ≥0∞; cS and occ have measurable fibres; reason: cS and occ take countably many values, so fibre measurability makes every cost measurable
--   - encoding: cells {0, ..., m-1} indexed cyclically, words of x numbered 1..|x| → Fin m with the forward distance cdist, words numbered 0..|x|-1; reason: index base and cyclic arithmetic only
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 10, Lemma 3.2 (PDF 11)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Static

open MeasureTheory
open scoped ENNReal

namespace CatalanHashing.Dynamic

/-- Lemma 3.2 (negative queries versus positive queries). In a static Catalan table whose
(random) placement follows an arbitrary rule, if every stored item `x` has expected positive
query scan cost at most `C |x|`, then a negative query for a key whose canonical cell is
uniform and independent of the table has expected scan cost at most `1 + C`. -/
theorem lemma_3_2 {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] (len : ι → ℕ)
    (hlen : ∀ x, 1 ≤ len x) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (cS : Ω → ι → Fin m) (occ : Ω → Occupancy m ι)
    (hcS : ∀ v : ι → Fin m, MeasurableSet {ω | cS ω = v})
    (hocc : ∀ o : Occupancy m ι, MeasurableSet {ω | occ ω = o})
    (hcat : ∀ ω, IsCatalanPlacement len (cS ω) (occ ω)) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x, ∫⁻ ω, (queryCost len (cS ω) (occ ω) (some x) (cS ω x) : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (C * len x)) :
    ∫⁻ p : Ω × Fin m, (queryCost len (cS p.1) (occ p.1) none p.2 : ℝ≥0∞)
        ∂(P.prod (PMF.uniformOfFintype (Fin m)).toMeasure) ≤ ENNReal.ofReal (1 + C) := by sorry

end CatalanHashing.Dynamic
