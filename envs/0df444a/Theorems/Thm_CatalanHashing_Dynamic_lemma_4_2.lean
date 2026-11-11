-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_lemma_4_2
-- name    : CatalanHashing.Dynamic.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:11.298201+00:00
-- url     : https://prove2.me/theorems/14f77927-51e5-4e53-b07b-e6805b78ed71
-- title:
--   Lemma 4.2 — the run of H_Y containing c(x) has E[W_x] = O(|x|) and E[W_x²] = O(|x|²), constant depending only on the load bound
-- statement:
--   Fix a load bound $\alpha<1$. There is a constant $C$, depending only on $\alpha$, with the following property. Let $S$ be a finite set of items ($|y|\ge1$) in an $m$-cell table with $\sum_{y\in S}|y|\le\alpha m$, the hashes independent and uniform, and let $x\in S$. Let $Y=\{y\in S:|y|\le|x|\}$, let $H_Y$ be the simple Catalan table on $Y$ (shorter items first, ties to the smaller hash), and let $W_x$ be the length of the run of $H_Y$ containing $c(x)$. Then
--   $$\mathbb E[W_x]\le C|x|\qquad\text{and}\qquad\mathbb E[W_x^2]\le C|x|^2.$$
--   The second-moment bound is used again for the erasure-coded tables of Sections 5-6 and their deletion variants.
--
--   Differences from the source:
--
--   - reading: E[W_x] = O(|x|) and E[W_x^2] = O(|x|^2), "a constant C (depending only on the load factor)" (p. 13) → ∀ α < 1, ∃ C, ∀ m ≥ 1, ι, len, load ≤ α, x: E[W_x] ≤ C|x| ∧ E[W_x^2] ≤ C|x|^2; reason: the O(·) constants depend on α only; one constant for both bounds is equivalent (take the maximum)
--   - encoding: h uniform on the continuous circle [0, m), canonical cell ⌊h(x)⌋ → h uniform on [0, 1] (unitInterval), canonical cell ⌊m h(x)⌋ capped at m - 1; reason: rescaling by m; [0, 1] and [0, 1) differ by a null set, and the cap only acts on the null event h = 1
--   - reading: "the run in H_Y containing c(x)" → runLength of the occupied cells of H_Y at c(x): the length of the maximal cyclic interval of occupied cells containing c(x) (m if every cell is occupied); reason: literal; the full-circle case cannot occur at load α < 1
--   - encoding: expectations → lintegrals over the product of uniform measures on the hashes; reason: W_x is a finite-valued measurable function of finitely many hashes
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 12, Lemma 4.2 (PDF 13)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Static

open MeasureTheory
open scoped ENNReal

namespace CatalanHashing.Dynamic

/-- Lemma 4.2. For every load bound `α < 1` there is a constant `C` (depending on `α` only) such
that, for every table and every item set of load at most `α` with independent uniform hashes,
the length `W_x` of the run of `H_Y` containing `c(x)` satisfies `E[W_x] ≤ C |x|` and
`E[W_x²] ≤ C |x|²`. -/
theorem lemma_4_2 (α : ℝ) (hα : α < 1) :
    ∃ C : ℝ, ∀ (m : ℕ) [NeZero m] (ι : Type) [Fintype ι] (len : ι → ℕ), (∀ x, 1 ≤ len x) →
      (∑ x, (len x : ℝ)) ≤ α * m → ∀ x : ι,
        ∫⁻ h : ι → unitInterval, (runLengthHY m len h x : ℝ≥0∞) ∂(Measure.pi fun _ => volume) ≤
            ENNReal.ofReal (C * len x) ∧
        ∫⁻ h : ι → unitInterval, ((runLengthHY m len h x : ℝ≥0∞) ^ 2)
            ∂(Measure.pi fun _ => volume) ≤ ENNReal.ofReal (C * (len x : ℝ) ^ 2) := by sorry

end CatalanHashing.Dynamic
