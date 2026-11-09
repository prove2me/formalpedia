-- Prove2me | Theorems.Thm_CubeSampling_lemma_C_5
-- name    : CubeSampling.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:23.671197+00:00
-- url     : https://prove2.me/theorems/3c97f9b4-49b1-46fd-a0b9-9fb84c59e562
-- title:
--   Lemma C.5 — Gaussian and chi-square tail bounds
-- statement:
--   **Lemma C.5.** Let $r \ge 1$ and $\chi^2_r = \sum_{j=1}^r G_j^2$ with $G_j$ i.i.d. $N(0,1)$. For $u \ge 0$ and $0 < a < 1$,
--   $$
--   P\bigl(\chi^2_r \ge 4(r+u)\bigr) \le e^{-u}, \tag{22}
--   $$
--   $$
--   P\bigl(\chi^2_r \le a r\bigr) \le \bigl(a e^{1-a}\bigr)^{r/2}. \tag{23}
--   $$
--   For a one-dimensional standard Gaussian $G$ and every $t \ge \log 4$,
--   $$
--   \frac{15}{16}\, e^{-t/256}\, P\bigl(G^2 \ge t/64\bigr) > e^{-t}. \tag{24}
--   $$
--
--   These are the probability estimates behind Corollary C.6 and Proposition E.2.
--
--   Differences from the source: none.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma C.5, (22)–(24), p.33

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Lemma C.5 (Gaussian and chi-square tail bounds) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma C.5, p.33): for `r ≥ 1` and
`χ²_r = ∑_{j ≤ r} G_j²` with `G_j` i.i.d. `N(0, 1)`: (22) `P(χ²_r ≥ 4(r + u)) ≤ e^{−u}` for `u ≥ 0`;
(23) `P(χ²_r ≤ ar) ≤ (a e^{1−a})^{r/2}` for `0 < a < 1`; (24) for a standard Gaussian `G` and every
`t ≥ log 4`, `(15/16) e^{−t/256} P(G² ≥ t/64) > e^{−t}`. -/
theorem lemma_C_5 (r : ℕ) (hr : 1 ≤ r) :
    (∀ u : ℝ, 0 ≤ u →
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) {G | 4 * (r + u) ≤ ∑ j, G j ^ 2} ≤
        ENNReal.ofReal (Real.exp (-u))) ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) {G | ∑ j, G j ^ 2 ≤ a * r} ≤
        ENNReal.ofReal ((a * Real.exp (1 - a)) ^ ((r : ℝ) / 2))) ∧
    (∀ t : ℝ, Real.log 4 ≤ t →
      Real.exp (-t) < 15 / 16 * Real.exp (-t / 256) * (gaussianReal 0 1).real {g | t / 64 ≤ g ^ 2}) := by sorry

end CubeSampling
