-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_proposition_2
-- name    : BinarySketchTruncation.Opposite.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:44.824245+00:00
-- url     : https://prove2.me/theorems/100e77d1-ece4-4a93-b521-698d57980adf
-- title:
--   Proposition 2 (corrected: zero-dimensional exception)
-- statement:
--   Fix $k\ge0$ and $p_0,p_1\in[0,1]$. Let $U\sim\operatorname{Bernoulli}(p_h)^{\otimes k}$ under hypothesis $h$. Let $V$ range over all vectors independent of $U$ conditional on each hypothesis, with arbitrary conditional laws $\nu_0,\nu_1$. The full characterization is
--
--   $$
--   [\,\forall(\nu_0,\nu_1),\ U\succeq U\oplus V\,]
--   \quad\Longleftrightarrow\quad
--   k=0\ \lor\ (p_0\le1/2\le p_1)\ \lor\ (p_1\le1/2\le p_0).
--   $$
--
--   Whenever the right side holds, the computed kernel $K$ in the explicit-kernel definition has nonnegative entries, each input row sums to one, and simultaneously for both hypotheses
--
--   $$
--   P_{U\oplus V,h}(s)=\sum_u P_{U,h}(u)K(s\mid u).
--   $$
--
--   The source's positive-dimensional result is unchanged. The zero-dimensional exception is necessary because the unique empty vector is unchanged by addition, including at the nonstraddling pair $p_0=p_1=1/4$. Equal biases are retained: for positive dimension the sufficient equal-bias case is exactly $p_0=p_1=1/2$, where identity is a valid kernel for every independent addition.
--
--   This milestone provides both the exact iff and the actual simulation witness required by the paper's statement.
--
--   Differences from the source:
--   - correction: the independent-addition iff has only the opposite-side condition → the right side is k=0 or the opposite-side condition; reason: at k=0 and p₀=p₁=1/4 every vector is empty, so identity simulates every independent addition although the biases do not straddle 1/2; Sections 2–3 impose no positive-dimension assumption
--   - encoding: finite binary vectors and hypothesis-indexed probability laws → Fin-indexed ZMod 2 vectors, Bool hypotheses, and normalized Mathlib PMFs; reason: these are the same finite objects and conditional laws; false denotes 0, true denotes 1, and addition is XOR
--   - encoding: the proof allows any coupling of the two added-vector laws and says the kernel is explicit → the theorem certifies the defined product-mixture kernel using their independent coupling, with identity branches at zero dimension and equal biases; reason: independent coupling is one permitted coupling; these branches cover the same sufficient regime while avoiding division by zero
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 7, Proposition 2, with explicit construction on p. 8 (PDF pp. 8–9)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_ExplicitKernel

namespace BinarySketchTruncation.Opposite

/-- Proposition 2, printed p. 7 (PDF 8), corrected at k=0.
Counterexample to the printed iff: k=0, p₀=p₁=1/4. All laws are the unique
empty-vector law, so identity simulates every independent sum, without opposite biases.
The second conjunct certifies the actual kernel from the proof on printed p. 8 (PDF 9). -/
theorem proposition_2 (k : ℕ) (p₀ p₁ : Bias) :
    ((∀ ν : Experiment (Vec k), Dominates (cubeExperiment k p₀ p₁)
        (independentSum (cubeExperiment k p₀ p₁) ν)) ↔
      k = 0 ∨ OppositeSides p₀ p₁) ∧
    ((k = 0 ∨ OppositeSides p₀ p₁) → ∀ ν : Experiment (Vec k),
      Simulates (cubeExperiment k p₀ p₁)
        (independentSum (cubeExperiment k p₀ p₁) ν)
        (explicitKernel k p₀ p₁ ν)) := by sorry

end BinarySketchTruncation.Opposite
