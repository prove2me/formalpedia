-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_11
-- name    : BinaryQueryLB.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:09.39731+00:00
-- url     : https://prove2.me/theorems/a7400d23-1bc9-4681-91f0-6d87ca1024fc
-- title:
--   Lemma 2.11 — exact quantiles of an affine function on a set of positive outer measure
-- statement:
--   Let $P\subseteq\mathbb R^m$ be bounded with $\mu^*(P)>0$ (not necessarily measurable), let $\ell(w)=c+\langle w,z\rangle$ with $c\in\mathbb R$ and $z\in\mathbb R^m\setminus\{0\}$, and let $\alpha\in(0,1)$. There is $r\in\mathbb R$ with
--   $$
--   \mu^*\big(P\cap\{\ell>r\}\big)=\alpha\,\mu^*(P)\qquad\text{and}\qquad\mu^*\big(P\cap\{\ell\le r\}\big)=(1-\alpha)\,\mu^*(P).
--   $$
--
--   The adversary uses these levels to cut the row sets by a prescribed fraction.
--
--   Differences from the source:
--   - encoding: Lebesgue outer measure µ* → MeasureTheory.volume evaluated on arbitrary sets, values in ℝ≥0∞; reason: volume on an arbitrary set is its outer measure
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.11, p.15

import Mathlib

namespace BinaryQueryLB

/-- **Lemma 2.11 (Quantiles).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.11, p.15: "Let `P ⊆ R^m` be bounded with `µ*(P) > 0`,
let `ℓ(w) = c + ⟨w, z⟩` with `c ∈ R` and `z ∈ R^m \ {0}`, and let `α ∈ (0, 1)`. There is `r ∈ R`
with `µ*(P ∩ {ℓ > r}) = α µ*(P)` and `µ*(P ∩ {ℓ ≤ r}) = (1 − α) µ*(P)`."

**Formalization Note.** `µ*` is `volume` on arbitrary sets (Lebesgue outer measure); `P` is not
assumed measurable. The products `α µ*(P)` are computed in `ℝ≥0∞`. -/
theorem lemma_2_11 (m : ℕ) (P : Set (EuclideanSpace ℝ (Fin m))) (hP : Bornology.IsBounded P)
    (hPpos : 0 < MeasureTheory.volume P) (c : ℝ) (z : EuclideanSpace ℝ (Fin m)) (hz : z ≠ 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ r : ℝ,
      MeasureTheory.volume (P ∩ {w | r < c + inner ℝ w z}) = ENNReal.ofReal α * MeasureTheory.volume P ∧
      MeasureTheory.volume (P ∩ {w | c + inner ℝ w z ≤ r}) =
        ENNReal.ofReal (1 - α) * MeasureTheory.volume P := by sorry

end BinaryQueryLB
