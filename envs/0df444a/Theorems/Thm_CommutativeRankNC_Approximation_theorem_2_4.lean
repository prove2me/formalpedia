-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_theorem_2_4
-- name    : CommutativeRankNC.Approximation.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:23.526212+00:00
-- url     : https://prove2.me/theorems/a2bce97c-7660-42c0-a84b-772e5ecef119
-- title:
--   Theorem 2.4 — Independent unbiased signs
-- statement:
--   For $m\ge2$, $t\ge1$, and any distinct $\alpha_i\in\mathbb F_q$, choose $a$ uniformly from $\mathbb F_q^t$ and set $\epsilon_i(a)=(-1)^{\operatorname{Tr}(p_a(\alpha_i))}$. The induced finite law is normalized, nonnegative, and satisfies
--
--   $$\Pr[\epsilon_{i_1}=\delta_1,\ldots,\epsilon_{i_s}=\delta_s]=2^{-s}$$
--
--   for every $s\le t$, every collection of distinct indices and every prescribed sign pattern $\delta_j\in\{-1,1\}$. Thus the signs are $t$-wise independent and unbiased. Repeated images of seeds keep their multiplicities.
--
--   Differences from the source:
--   - encoding: elements of the quotient field F₂[z]/(f) → binary coefficient representatives, finite trial division, and reduction modulo the first irreducible polynomial; reason: these are the explicit field representation and deterministic search in the proof of Lemma 2.1; no arithmetic oracle is used
--   - encoding: probabilities and expectations for a finite sign distribution → finite real weighted sums, with seed multiplicities retained in the pushforward law; reason: a finite law needs no analytic integrability assumption and does not replace the seed law by a uniform distinct-image law
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Theorem 2.4, PDF/printed p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Signs

namespace CommutativeRankNC.Approximation

/-- Theorem 2.4, PDF/printed p.11, with arbitrary distinct field points. -/
theorem theorem_2_4 (m t : ℕ) (hm : 2 ≤ m) (ht : 0 < t)
    (α : Fin m ↪ Fin (fieldCard m)) :
    TWiseUnbiased t (signWeightAt m t (fun i => (α i).val)) := by sorry

end CommutativeRankNC.Approximation
