-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_lemma_28
-- name    : ChvatalOneHard398.SAT.Supplement.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:07.176215+00:00
-- url     : https://prove2.me/theorems/ff6c6a91-dfa6-47fb-8211-350a3187ca2d
-- title:
--   Lemma 28 — congruence-kernel construction
-- statement:
--   Let $q$ be prime, let $n<m$, and let $A\in(\mathbb Z/q\mathbb Z)^{n\times m}$ be arbitrary. A fixed deterministic algorithm, polynomial in $m$ and $\log q$, computes a matrix $H\in\{0,\ldots,q-1\}^{m'\times m}$ with
--   $$1\le m'\le m,\qquad\Lambda_q^\perp(H)=\Lambda_q(A^T).$$
--   The equality is asserted both as a condition on every integer vector and after embedding in Euclidean space. No rank assumption on $A$ is needed.
--
--   This provides the congruence description used by the formula construction of Theorem 29.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time computations → the published binary TM2 next-step model and finite input records; reason: uniform time bounds charge for writing every query and output on every raw input
--   - encoding: uniform residues, independent errors and probabilities → canonical integral residues and genuine PMFs with nonnegative mass sums; reason: no rank conditioning, integrability defaults or nonmeasurable maps are introduced
--   - encoding: Gaussian elimination computes a kernel basis → first available pivots, free columns in increasing order and canonical residues; reason: this makes the source algorithm deterministic without selecting H by lattice equality
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.29, Lemma 28. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem lemma_28 :
    PolyTime encAryMatrix id (fun a => encKernel (kernelMatrix a)) ∧
    ∀ a : AryMatrix, a.q.Prime → a.n < a.m → a.Valid →
      1 ≤ (kernelMatrix a).r ∧ (kernelMatrix a).r ≤ a.m ∧
      (∀ i j, 0 ≤ (kernelMatrix a).H i j ∧ (kernelMatrix a).H i j < (a.q : ℤ)) ∧
      (∀ y : Fin a.m → ℤ, y ∈ congruenceKernel a.q (kernelMatrix a).H ↔ aryMember a y) ∧
      congruenceLattice a.q (kernelMatrix a).H = aryLattice a := by sorry

end ChvatalOneHard398.SAT.Supplement
