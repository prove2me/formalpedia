-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_theorem_1
-- name    : BinarySketchTruncation.Opposite.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:40.384983+00:00
-- url     : https://prove2.me/theorems/4954b663-e76e-4ce5-bcc3-af7b363486d4
-- title:
--   Theorem 1 — truncation is optimal for testing opposite correlations
-- statement:
--   Let $p_0,p_1\in[0,1]$ satisfy $p_0\le1/2\le p_1$ or $p_1\le1/2\le p_0$. Let $A$ and $B$ be arbitrary binary matrices with $n$ columns (any numbers of rows) of ranks $k_A=\operatorname{rank}A$ and $k_B=\operatorname{rank}B$ over $\mathbb F_2$, and put $k=\min\{k_A,k_B\}$. Under hypothesis $h$, draw uniform $X\in\mathbb F_2^n$ independently of $Z\sim\operatorname{Bernoulli}(p_h)^{\otimes n}$ and set $Y=X\oplus Z$. Then
--
--   $$
--   (X_{[k]},Y_{[k]})\succeq(AX,BY).
--   $$
--
--   Here $[k]$ denotes the first $k$ coordinates. There exists one normalized stochastic kernel from the paired prefix to the paired sketches that realizes their laws under both hypotheses. Thus the entire attainable type-I/type-II error trade-off for the sketches is attainable from the common prefix.
--
--   The statement includes unequal ranks, zero-dimensional observations, every endpoint bias, both orientations of the closed opposite-side condition, and $p_0=p_1=1/2$. No asymptotic limit or distinct-bias assumption is imposed.
--
--   Differences from the source:
--   - encoding: finite binary vectors and hypothesis-indexed probability laws → Fin-indexed ZMod 2 vectors, Bool hypotheses, and normalized Mathlib PMFs; reason: these are the same finite objects and conditional laws; false denotes 0, true denotes 1, and addition is XOR
--   - generalization: a rank-k_A matrix, taken w.l.o.g. with full row rank (Definition 1 preamble, so k_A rows) → any binary matrix with n columns and any number of rows, with k_A := its rank; reason: a full-row-rank k_A-row matrix has rank k_A, so the source's normalized statement is the special case; the Lean also covers the theorem's literal wording "rank-k_A matrix" without the w.l.o.g. reduction
--   - encoding: paired first-k-coordinate truncation, with k≤n → the total takePrefix definition is zero-padded when k>n, and is ordinary restriction for every admitted matrix pair; reason: no extra dimension hypothesis is added and no source instance changes, since k=min(rank A, rank B)≤n always
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 6, Theorem 1; standing model on p. 5 (PDF pp. 6–7)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite

/-- Theorem 1, printed p. 6 (PDF 7), at full strength.
A and B are arbitrary binary matrices with n columns, of ranks kA = A.rank and
kB = B.rank (rows need not be independent). Since rank ≤ n, min kA kB ≤ n and
takePrefix restricts to the first min kA kB coordinates with no padding. -/
theorem theorem_1 {n mA mB : ℕ} (p₀ p₁ : Bias)
    (hop : OppositeSides p₀ p₁)
    (A : Matrix (Fin mA) (Fin n) Bit) (B : Matrix (Fin mB) (Fin n) Bit) :
    Dominates (prefixExperiment n (min A.rank B.rank) p₀ p₁)
      (sketchExperiment p₀ p₁ A B) := by sorry

end BinarySketchTruncation.Opposite
