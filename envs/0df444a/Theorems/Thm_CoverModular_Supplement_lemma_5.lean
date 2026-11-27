-- Prove2me | Theorems.Thm_CoverModular_Supplement_lemma_5
-- name    : CoverModular.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:18:45.299964+00:00
-- url     : https://prove2.me/theorems/49bbf2f8-9c0a-4db2-87ed-fe51f40b6ec9
-- title:
--   Lemma 5 — for an integer matrix, rounding the right-hand side down does not change $P(b)$ or any integer program over it
-- statement:
--   Let $(a_{ij})$ be a matrix with entries $a_{ij}\in\mathbb Z$ ($1\le i\le m$, $1\le j\le n$), let $b\in\mathbb R^m$, and define
--
--   $$
--   P(b)=\Big\{x\in\mathbb Z^n\ \Big|\ \sum_ja_{ij}x_j\le b_i,\ 1\le i\le m\Big\}.
--   $$
--
--   Let $\lfloor b\rfloor$ denote $b$ rounded down to the nearest integer element-wise. Then
--
--   1. $P(b)=P(\lfloor b\rfloor)$;
--   2. for every $c\in\mathbb R^n$,
--
--   $$
--   \max\Big\{\sum_jc_jx_j\ \Big|\ x\in P(b)\Big\}=\max\Big\{\sum_jc_jx_j\ \Big|\ x\in P(\lfloor b\rfloor)\Big\}.
--   $$
--
--   In the proof of Theorem 2 this lets the integer program with right-hand side $b$ be replaced by the one with right-hand side $\lfloor b\rfloor$. That program has integral data, so total unimodularity identifies it with its LP relaxation.
--
--   **Formalization Note** The equality of maxima is stated for every real $v$: $v$ is the greatest objective value over $P(b)$ if and only if it is the greatest over $P(\lfloor b\rfloor)$. So one maximum exists exactly when the other does, and then the two are equal. No attainment is assumed.
--
--   Differences from the source:
--   - reading: max{Σ_j c_j x_j | x ∈ P(b)} = max{Σ_j c_j x_j | x ∈ P(⌊b⌋)} for all c → for all c and v, v is the greatest value over P(b) iff v is the greatest value over P(⌊b⌋); reason: the maxima need not exist (P(b) empty or the objective unbounded), and this reading asserts that they exist together and are then equal
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, Lemma 5, p.43

import Mathlib
import Definitions.Def_CoverModular_Supplement_intPoints

namespace CoverModular.Supplement

/-- **Lemma 5** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, Appendix A.3, Lemma 5, p.43). For an integer matrix `a_ij ∈ ℤ` and `b ∈ ℝ^m`,
with `P(b) = {x ∈ ℤⁿ | ∑_j a_ij x_j ≤ b_i, 1 ≤ i ≤ m}` and `⌊b⌋` the element-wise floor,
`P(b) = P(⌊b⌋)`, and for every `c ∈ ℝⁿ`,
`max{∑_j c_j x_j | x ∈ P(b)} = max{∑_j c_j x_j | x ∈ P(⌊b⌋)}`.

**Formalization Note** The equality of maxima is stated for every candidate value `v`: `v` is the
greatest objective value over `P(b)` iff it is the greatest over `P(⌊b⌋)`. So one maximum exists
iff the other does, and then they are equal; no attainment is assumed. -/
theorem lemma_5 {m n : ℕ} (a : Fin m → Fin n → ℤ) (b : Fin m → ℝ) :
    intPoints a b = intPoints a (fun i => (⌊b i⌋ : ℝ)) ∧
      ∀ (c : Fin n → ℝ) (v : ℝ),
        IsGreatest ((fun x : Fin n → ℤ => ∑ j, c j * (x j : ℝ)) '' intPoints a b) v ↔
          IsGreatest ((fun x : Fin n → ℤ => ∑ j, c j * (x j : ℝ)) ''
            intPoints a (fun i => (⌊b i⌋ : ℝ))) v := by sorry

end CoverModular.Supplement
