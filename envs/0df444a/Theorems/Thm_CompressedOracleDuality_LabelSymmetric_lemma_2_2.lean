-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_lemma_2_2
-- name    : CompressedOracleDuality.LabelSymmetric.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:03:35.875849+00:00
-- url     : https://prove2.me/theorems/69d13742-00c2-4731-843e-6eadf01c0433
-- title:
--   Lemma 2.2 — pure-ensemble measurement information
-- statement:
--   Let $I,J$ and the Hilbert-space basis be finite. Let $p_i\ge0$ sum to one, let $|\psi_i\rangle$ be unit pure states, and let $E_j$ be positive semidefinite measurement effects summing to the identity. Write $r$ for the dimension of the linear span of all the $\psi_i$. Define the joint ensemble–measurement law by $P(i,j)=p_i\langle\psi_i|E_j|\psi_i\rangle$. Then
--   $$I(I;J)\le\log_2 r.$$
--   This is the dimension form of the measurement information bound used for the database ensemble. All probabilities are finite sums, including zero-prior terms.
--
--   Differences from the source:
--   - encoding: POVM on the span of the pure states → POVM on an ambient finite coordinate space with the same span dimension r; reason: restriction to the span preserves every outcome probability; a span POVM extends by assigning the orthogonal complement to one outcome
--   - reading: POVM {E_j}_j with its outcome set unspecified → finite outcome type J; reason: §2.1 takes its information facts from [Wat18, Chapter 5], whose measurements have finite outcome alphabets; a countable POVM is covered too, since its information is the supremum over finite coarse-grainings, each a POVM
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 12, Lemma 2.2, (11)–(12)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Measurement

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- Lemma 2.2, p.12: the ensemble spans a subspace of dimension r. -/
theorem lemma_2_2 {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι] [DecidableEq ι]
    (p : I → ℝ) (ψ : I → EuclideanSpace ℂ ι) (E : J → Matrix ι ι ℂ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hψ : ∀ i, IsState (ψ i))
    (hE : IsPOVM E) :
    mutualInfoBits (fun ij : I × J => p ij.1 * (inner ℂ (ψ ij.1) (act (E ij.2) (ψ ij.1))).re) ≤
      Real.logb 2 (Module.finrank ℂ (Submodule.span ℂ (Set.range ψ))) := by sorry

end CompressedOracleDuality.LabelSymmetric
