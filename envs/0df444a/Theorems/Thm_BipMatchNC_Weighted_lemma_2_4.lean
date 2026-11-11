-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_lemma_2_4
-- name    : BipMatchNC.Weighted.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:12:03.898929+00:00
-- url     : https://prove2.me/theorems/3980793d-80b6-4dd0-8e98-aeef0c682e4f
-- title:
--   Lemma 2.4 (folded Wronskian criterion): polynomials of degree ≤ d are linearly independent iff their γ-folded Wronskian has nonzero determinant, when γ has order > d
-- statement:
--   Let $F$ be a field, $d\in\mathbb N$, and let $\gamma\in F$ have multiplicative order more than $d$ ($\gamma\ne0$ and $\gamma^k\ne1$ for $1\le k\le d$). For polynomials $p_1,\dots,p_s\in F[x]$ of degree at most $d$, let $W_\gamma(p_1,\dots,p_s)$ be the $s\times s$ matrix with row $j$ equal to $(p_1(\gamma^jx),\dots,p_s(\gamma^jx))$, $0\le j\le s-1$. Then
--   $$p_1,\dots,p_s \text{ are linearly independent over } F\iff \det W_\gamma(p_1,\dots,p_s)(x)\neq0 \text{ in } F[x].$$
--
--   This is the folded analogue of the classical Wronskian criterion, and it replaces derivatives by the shifts $x\mapsto\gamma^jx$, so it works in every characteristic. It drives the root bound of Lemma 2.6.
--
--   Differences from the source:
--   - encoding: γ has order more than d → OrderAtLeast γ (d + 1): γ ≠ 0 and γ ^ k ≠ 1 for 0 < k ≤ d (infinite order included); reason: multiplicative order; an element of order > d is a nonzero element
--   - encoding: p_1(x), …, p_s(x) of degree at most d, linearly independent → a family p : Fin s → F[X] with natDegree (p i) ≤ d, and LinearIndependent F p; reason: the zero polynomial has natDegree 0 ≤ d and is dependent either way; a repeated polynomial makes the family dependent, as for a list
--   - encoding: det(W_γ(p_1, …, p_s))(x) is a nonzero polynomial → (foldedWronskian γ p).det ≠ 0, with entry (j, i) = (p i).comp (C (γ ^ j) * X); reason: same matrix, rows indexed from 0
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 6 (PDF 7), Lemma 2.4; proof in Appendix B, p. 60 (PDF 61)

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded

open Polynomial

namespace BipMatchNC.Weighted

theorem lemma_2_4 {F : Type*} [Field F] (γ : F) (d s : ℕ) (p : Fin s → F[X])
    (hdeg : ∀ i, (p i).natDegree ≤ d) (hγ : OrderAtLeast γ (d + 1)) :
    LinearIndependent F p ↔ (foldedWronskian γ p).det ≠ 0 := by sorry

end BipMatchNC.Weighted
