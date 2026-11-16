-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_lemma_3
-- name    : BinarySketchTruncation.Opposite.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:32.59294+00:00
-- url     : https://prove2.me/theorems/6e3f83eb-7441-40ad-a927-2f7393f5b692
-- title:
--   Lemma 3 — conditional variance for bipartite connectivity
-- statement:
--   Let a,b ≥ 0 be integers, m=a·b, and let G(Z) be the uniform random spanning subgraph of the complete bipartite graph K_{a,b}. Its edge vector Z is uniform on 𝔽₂ᵐ. Let f(Z)=1{G(Z) is connected}, with connectivity on all a+b vertices. For every set I of possible edges,
--
--   $$
--   m\,\operatorname{Var}\bigl(\mathbb E[f(Z)\mid Z_I]\bigr)
--    \le |I|\,\operatorname{Var}(f(Z)).
--   $$
--
--   Conditional expectation is the average over the complete fiber of the observed edge coordinates. This bounds the variance explained by any set of observed edges and supports the linear-sketch lower bound in Theorem 3. It applies to every complete bipartite graph, including zero-edge cases.
--
--   Differences from the source:
--   - encoding: Var(E[f | Z_I]) ≤ (|I|/m) Var(f) → m Var(E[f | Z_I]) ≤ |I| Var(f), including m=0; reason: equivalent for m>0; when m=0 the only edge set is empty, both sides are zero and the connectivity indicator is constant
--   - encoding: uniform edge vector, conditional expectation and variance → pair-indexed ZMod 2 edge vectors and finite real averages over coordinate fibers; reason: these give the identical uniform law and conditioning, retain all vertices, and have positive averaging denominators even when a or b is zero
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 12 (PDF p. 13), Lemma 3; restated p. 18 (PDF p. 19), with proof p. 19 (PDF p. 20), Appendix A.2

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_Connectivity

namespace BinarySketchTruncation.Opposite.Supplement

/-- Lemma 3, printed p. 12 (PDF 13), restated p. 18 (PDF 19).
Multiplication by m removes the division; when m=0 both sides are zero. -/
theorem lemma_3 (a b : ℕ) (I : Finset (Fin a × Fin b)) :
    (a * b : ℕ) * uniformVariance
      (coordinateConditionalMean (connectivityIndicator (a := a) (b := b)) I) ≤
    (I.card : ℝ) * uniformVariance (connectivityIndicator (a := a) (b := b)) := by sorry

end BinarySketchTruncation.Opposite.Supplement
