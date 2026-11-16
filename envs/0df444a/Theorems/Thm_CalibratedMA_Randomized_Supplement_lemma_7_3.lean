-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_7_3
-- name    : CalibratedMA.Randomized.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:59.067262+00:00
-- url     : https://prove2.me/theorems/2e983ab7-b108-4a89-85ed-8910f6034d57
-- title:
--   Lemma 7.3 — A small family of sign tests detects ℓ_1 error
-- statement:
--   There are positive universal constants $a_*,A_*,c_*,C_*$. For each integer $N\ge2$ and every real $K_{\rm test}$ in the entire interval $A_*\log N\le K_{\rm test}\le a_*N$, there is a finite set of actual sign functions $G\subseteq\{-1,1\}^{[N]}$ satisfying
--   $$\exp(c_*K_{\rm test})\le|G|\le\exp(C_*K_{\rm test})$$
--   and, simultaneously for every $d\in\mathbb R^N$,
--   $$\max_{g\in G}\left|\sum_{i=1}^Ng_i d_i\right|\ge c_*\sqrt{K_{\rm test}/N}\sum_{i=1}^N|d_i|.$$
--   No multiplicity is counted in $|G|$. This finite testing result supports the prescribed group budget in Theorem 7.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: a maximum over the finite sign-test family → for every vector there exists a test attaining at least the bound; reason: equivalent to the maximum inequality on the finite nonempty family; cardinality counts distinct functions
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 38, Lemma 7.3 (PDF pp. 40)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 7.3, p.38: one set of actual functions works for every real vector. -/
theorem lemma_7_3 :
    ∃ a A c C : ℝ, 0 < a ∧ 0 < A ∧ 0 < c ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ Ktest : ℝ,
      A * Real.log N ≤ Ktest → Ktest ≤ a * N →
      ∃ G : Finset (Fin N → ℝ),
        (∀ g ∈ G, ∀ i, IsSign (g i)) ∧
        Real.exp (c * Ktest) ≤ (G.card : ℝ) ∧
        (G.card : ℝ) ≤ Real.exp (C * Ktest) ∧
        ∀ d : Fin N → ℝ, ∃ g ∈ G,
          |∑ i : Fin N, g i * d i| ≥
            c * Real.sqrt (Ktest / N) * ∑ i : Fin N, |d i| := by sorry

end CalibratedMA.Randomized.Supplement
