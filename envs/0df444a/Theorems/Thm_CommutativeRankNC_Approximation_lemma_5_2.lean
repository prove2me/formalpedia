-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_5_2
-- name    : CommutativeRankNC.Approximation.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:38.889363+00:00
-- url     : https://prove2.me/theorems/2119396d-74d5-44a0-90e4-fcba056b533d
-- title:
--   Lemma 5.2 — Truncated Schur rank upper bound
-- statement:
--   For arbitrary rational $n\times n$ matrices $A,C$, let $r=\operatorname{rank}A$, choose any rank normalization of $A$, and apply the same transformations to $C$. For every $k\ge1$, writing $s=\operatorname{rank}_{\mathbb Q(t)}(A+tC)-r$,
--
--   $$\operatorname{rank}_{\mathbb Q}J_k(A,C)\le ks.$$
--
--   The increment $s$ is represented by a signed difference. No positive-deficit or membership condition on $C$ is added. This bounds how much truncated rank can arise from a scalar pencil.
--
--   Differences from the source:
--   - generalization: the scalar direction C=B(b) in the section's matrix-space setting → arbitrary rational matrices A and C, also in dimension zero; reason: the Smith-form proof on p.22 uses only the rational pair and a rank normalization; every source pair is included, and the zero-dimensional inequality is 0≤0
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: the rank increment s → the integer difference of the actual generic pencil rank and rank A; reason: this avoids natural subtraction silently deleting a negative input and keeps the actual pencil tied to C
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 5.2, PDF/printed p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Lemma 5.2, PDF/printed p.22, all scalar directions with the same
normalization; the generic rank increment is a signed integer. -/
theorem lemma_5_2 {n : ℕ} (A C : QMatrix n) (S : Normalization A)
    (k : ℕ) (hk : 0 < k) :
    ((scalarJ S C k).rank : ℤ) ≤
      (k : ℤ) * (((affinePencil A C).rank : ℤ) - (S.r : ℤ)) := by sorry

end CommutativeRankNC.Approximation
