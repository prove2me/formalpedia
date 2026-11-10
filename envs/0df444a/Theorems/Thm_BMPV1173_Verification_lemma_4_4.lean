-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_4
-- name    : BMPV1173.Verification.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:12.011575+00:00
-- url     : https://prove2.me/theorems/27cbb21c-ccb3-4699-ae8e-447962182213
-- title:
--   Lemma 4.4 — rounded size labels and all class bounds
-- statement:
--   Fix left lists satisfying $\sum_i|\mathrm{Left}_i|\le100n^3/(st)$ before drawing the independent coordinate sample $K$. Compute each $\mathrm{size}_i$ by rounding the estimator in (4.4), equivalently (4.19), upward to a power of two; let $V_a$ be its class. With probability at least $1-2n^{-3}$,
--   $$|\mathrm{Left}_i|\le\mathrm{size}_i\le8(|\mathrm{Left}_i|+t),\qquad a|V_a|\le\sum_i\mathrm{size}_i\le8nt+\frac{800n^3}{st}.$$
--   There are $O(\log n)$ nonempty classes, with a universal coefficient; the bound uses $1+\log n$ to include $n=1$. All inequalities hold jointly, not with separate per-index probabilities. Fixing arbitrary lists before the independent sample also expresses the source conditional probability statement.
--
--   Differences from the source:
--   - encoding: independent uniform samples with replacement and sufficiently large absolute sampling constants → uniform probability on ordered draw tuples and ceiling lengths c(n/t)(1+log n); reason: ordered tuples keep every repeated occurrence, and the positive-dimension boundary is defined without changing the asymptotic sampling scale
--   - generalization: left lists constructed during preprocessing → arbitrary fixed left lists satisfying the same total-size bound; reason: conditioning on preprocessing gives precisely such lists, and the label-sampling statement uses no other property of their construction
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.4, printed p.24 = PDF p.24.

import Definitions.Def_BMPV1173_Verification_Preprocessing

namespace BMPV1173.Verification

open scoped BigOperators

/-- Size labels, including every inequality in (4.6) and the number of classes.
The left lists may be fixed arbitrarily before drawing the independent coordinate sample;
this includes conditioning on the preprocessing, as on p.29. Source pp.23–24. -/
theorem lemma_4_4 :
    ∃ (c : ℕ) (C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ (n s t : ℕ), 1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
      ∀ L : Fin n → Finset (Fin n),
      (∑ i : Fin n, ((L i).card : ℝ)) ≤ 100*(n : ℝ)^3/((s : ℝ)*t) →
      uniformProbability (fun K : Fin (sampleCount c n t) → Fin n => sizeGood L s t K) ≥
        1 - 2 * (n : ℝ)^(-3 : ℝ) ∧
      ∀ K : Fin (sampleCount c n t) → Fin n,
        ((classLabels L t K).card : ℝ) ≤ C*(1+Real.log (n : ℝ)) := by sorry

end BMPV1173.Verification
