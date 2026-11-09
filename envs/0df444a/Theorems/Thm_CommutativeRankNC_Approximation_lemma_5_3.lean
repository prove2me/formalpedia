-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_5_3
-- name    : CommutativeRankNC.Approximation.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:34.459558+00:00
-- url     : https://prove2.me/theorems/ffc61ae1-c244-4909-8794-d644ab65ef51
-- title:
--   Lemma 5.3 — Integer specialization realizes rank
-- statement:
--   For every pair of rational $n\times n$ matrices $A,C$, an integer $\lambda$ in exactly the set $\{0,1,\ldots,n\}$ realizes the generic pencil rank:
--
--   $$\exists\lambda\in\{0,\ldots,n\}:\quad\operatorname{rank}_{\mathbb Q}(A+\lambda C)=\operatorname{rank}_{\mathbb Q(t)}(A+tC).$$
--
--   There is no requirement that the matrices lie in a particular matrix space. This supplies the finite scalar candidate range used by every boosting round.
--
--   Differences from the source:
--   - generalization: rational n×n matrices in the positive-dimensional setting → also zero-dimensional rational matrices; reason: the extra case has generic and specialized rank zero, with λ=0; there is no generating-list parameter in this statement
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: λ in {0,…,n} → a natural number λ with λ≤n, cast to Q in the matrix; reason: the finite candidate set is identical, including both endpoints
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 5.3, PDF/printed p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Lemma 5.3, PDF/printed p.22: exactly the n+1 integer substitutions. -/
theorem lemma_5_3 {n : ℕ} (A C : QMatrix n) :
    ∃ l : ℕ, l ≤ n ∧ (A + (l : ℚ) • C).rank = (affinePencil A C).rank := by sorry

end CommutativeRankNC.Approximation
