-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_classical_conditional_bias
-- name    : BooleanHiddenPartition.LowerBounds.classical_conditional_bias
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:23:07.367061+00:00
-- url     : https://prove2.me/theorems/43f84d98-af31-4c62-9b4c-3c3c65104917
-- title:
--   Lemma 8 — Conditional single-block squared bias
-- statement:
--   Fix k>0 and alpha in (0,1). A constant K>0 depends only on k and alpha. For every 1≤d≤k, Boolean f and mass q satisfying the vanishing correlations below d, every admissible layout, and every deterministic c-bit encoder, let p be the actual posterior given sigma and the received message. If F_z^i fixes the outputs of all blocks before block i, then for every block and every such prefix,
--
--   $$\mathbb E_{\sigma,a\mid F_z^i}[(\mathbb E_{p\mid F_z^i} f(x^i))^2]\leq K(c/n)^d.$$
--
--   The source fixes the randomness before this lemma (p.15); the general randomized success bound is a separate item. The zero-message case is included. Neither the posterior nor the conditioning law is a free parameter.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: Positive source parameters with alpha n/k an integer → A positive integer m and Layout with k*m=alpha*n; reason: This is the same admissibility condition without truncating division; irrational alpha retains the source admissibility quantifier.
--   - encoding: An O-bound with the dependencies specified in the text → A positive existential constant before every varying datum; reason: This spells out the source uniformity without choosing a numeral or weakening a power.
--   - encoding: The displayed 1/d and 2/d → The defined domain d>0; reason: The printed expressions have no ordinary value at d=0; all cases with defined exponents are retained.
--   - encoding: Conditional distributions and states under the hard law → Explicit normalized masses and entrywise matrix averages, zero on null events; reason: These are the actual constructed source objects; null events contribute zero to the expectations.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 16, Lemma 8.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Lemma 8, p.16, with the standing hard-law hypotheses of §3.2. -/
theorem classical_conditional_bias (k : ℕ) (hk : 0 < k) (α : ℝ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ), 0 < d → d ≤ k →
      ∀ (f : Cube k → Bool) (q : Cube k → ℝ), IsMass q → moments f q d →
      ∀ (n m c : ℕ) (L : Layout k n m α) (e : Cube n → Fin (2 ^ c))
        (i : Fin m) (z : Cube i.val),
        classicalBias L f q e i z ≤ K * ((c : ℝ) / n) ^ d := by sorry

end

end BooleanHiddenPartition.LowerBounds
