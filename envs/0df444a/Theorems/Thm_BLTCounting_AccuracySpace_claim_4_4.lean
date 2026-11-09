-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_claim_4_4
-- name    : BLTCounting.AccuracySpace.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:00.357376+00:00
-- url     : https://prove2.me/theorems/f18978b4-5258-415c-b55c-9821b4ad66b4
-- title:
--   Harmonic block mass
-- statement:
--   Let $R\ge1$ be an integer, let $0<h\le1$, and let $w_i=\sum_{r\in S_i}1/r$ be the harmonic mass of the geometric block $S_i$. Then, with an absolute implied constant, uniformly in $i$,
--   $$w_i=h+O\!\left(\frac1R\right)=h\bigl(1+O((Rh)^{-1})\bigr).$$
--   Each block therefore carries nearly the same harmonic mass $h$, which is why $Q$ acts on a uniform logarithmic scale.
--
--   **Formalization Note.** The two $O$ terms are stated as $|w_i-h|\le C/R$ and $|w_i/h-1|\le C/(Rh)$, with one constant $C>0$ chosen before $R$, $h$ and $i$.
--
--   Differences from the source:
--   - generalization: the parameters $R$, $h$ of equation (28) and block indices $i<K$ → all integers $R\ge1$, all $0<h\le1$ and all $i\in\mathbb N$; reason: the estimate depends only on these ranges; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 4.4, printed p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks

namespace BLTCounting.AccuracySpace

/-- Claim 4.4, PDF p. 27: `w_i = h + O(1/R) = h(1 + O((Rh)⁻¹))`, with an absolute implied constant,
uniformly in the block index `i`, the integer `R ≥ 1` and the width `0 < h ≤ 1`. -/
theorem claim_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (h : ℝ), 1 ≤ R → 0 < h → h ≤ 1 → ∀ i : ℕ,
      |blockMass R h i - h| ≤ C / R ∧ |blockMass R h i / h - 1| ≤ C / (R * h) := by sorry

end BLTCounting.AccuracySpace
