-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_proposition_1
-- name    : BinarySketchTruncation.Opposite.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:23.767051+00:00
-- url     : https://prove2.me/theorems/513203fb-330b-48c3-8a9e-5a1d6848d515
-- title:
--   Proposition 1 — same linear sketch is always better
-- statement:
--   Let $p_0,p_1\in[0,1]$, and let $A,B$ be arbitrary binary matrices with $n$ columns, with no row-rank restriction. Under hypothesis $h$, independently draw uniform $X\in\mathbb F_2^n$ and $Z\sim\operatorname{Bernoulli}(p_h)^{\otimes n}$ and set $Y=X\oplus Z$. Then both comparisons hold:
--
--   $$
--   A(X\oplus Y)=AX\oplus AY\succeq(AX,BY),\qquad
--   B(X\oplus Y)=BX\oplus BY\succeq(AX,BY).
--   $$
--
--   Each dominance comparison has one normalized kernel that works for both hypotheses. The two displayed matrix identities hold pointwise for every pair of input vectors. No opposite-side condition on the biases is needed.
--
--   This compares different terminal sketches against each terminal's common-sum statistic, including matrices with dependent rows and empty sketches.
--
--   Differences from the source:
--   - encoding: finite binary vectors and hypothesis-indexed probability laws → Fin-indexed ZMod 2 vectors, Bool hypotheses, and normalized Mathlib PMFs; reason: these are the same finite objects and conditional laws; false denotes 0, true denotes 1, and addition is XOR
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 6, Proposition 1 (PDF p. 7)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite

/-- Proposition 1, printed p. 6 (PDF 7). No rank or opposite-side assumptions. -/
theorem proposition_1 {n kA kB : ℕ} (p₀ p₁ : Bias)
    (A : Matrix (Fin kA) (Fin n) Bit) (B : Matrix (Fin kB) (Fin n) Bit) :
    (∀ x y : Vec n, A.mulVec (x + y) = A.mulVec x + A.mulVec y) ∧
    (∀ x y : Vec n, B.mulVec (x + y) = B.mulVec x + B.mulVec y) ∧
    Dominates (sumSketchExperiment p₀ p₁ A) (sketchExperiment p₀ p₁ A B) ∧
    Dominates (sumSketchExperiment p₀ p₁ B) (sketchExperiment p₀ p₁ A B) := by sorry

end BinarySketchTruncation.Opposite
