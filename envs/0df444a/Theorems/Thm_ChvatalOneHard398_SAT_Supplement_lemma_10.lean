-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_lemma_10
-- name    : ChvatalOneHard398.SAT.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:38.606806+00:00
-- url     : https://prove2.me/theorems/d397f05c-e9e6-4116-8d93-3c932c897097
-- title:
--   Lemma 10 — random q-ary minimum
-- statement:
--   Let $q$ be prime and let $A\in(\mathbb Z/q\mathbb Z)^{n\times m}$ have independent uniform entries. For the full-rank lattice $L=\Lambda_q(A^T)$,
--   $$\Pr\{\lambda_1(L)>q/8\}\ge 1-q^n2^{-m}.$$
--
--   No full-row-rank condition is imposed on $A$. This probability estimate is shared by both average-case companion theorems.
--
--   Differences from the source:
--   - encoding: uniform residues, independent errors and probabilities → canonical integral residues and genuine PMFs with nonnegative mass sums; reason: no rank conditioning, integrability defaults or nonmeasurable maps are introduced
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.14, Lemma 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem lemma_10 (n m q : ℕ) (hq : q.Prime) :
    1 - (q : ℝ)^n * (2 : ℝ)^(-(m : ℤ)) ≤
      prob (matrixLaw n m q) (fun a =>
        (q : ℝ)/8 < RegevLWE.SmoothingLB.lambda1 (aryLattice a)) := by sorry

end ChvatalOneHard398.SAT.Supplement
