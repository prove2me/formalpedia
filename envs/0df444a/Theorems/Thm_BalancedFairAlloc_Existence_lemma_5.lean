-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_5
-- name    : BalancedFairAlloc.Existence.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:38.794126+00:00
-- url     : https://prove2.me/theorems/0ef88c23-7214-4bfb-be77-d2c285a6ba4f
-- title:
--   Lemma 5 — price interlacing between any two score maximizers
-- statement:
--   Assume $n\ge2$ and $r\ge1$. Fix weights $\alpha\in\mathbb R^n$, prices $p\in\mathbb R^M$ and $\varepsilon>0$, and let $R$ be the set of maximizers of the score
--
--   $$S(A)=\sum_i\alpha_iv_i(A_i)+\varepsilon\,\Phi_p(A)$$
--
--   over balanced integral allocations, with $\Phi_p$ the prefix potential (12). For any $A,B\in R$ and any agent $i$, let $a_1\ge a_2\ge\cdots$ and $b_1\ge b_2\ge\cdots$ be the positive-price profiles of $A_i$ and $B_i$, padded with zeros. Then $a_{\ell+1}\le b_\ell$ and $b_{\ell+1}\le a_\ell$ for every $\ell\ge1$, and the same inequalities hold for the negative-price magnitude profiles of $A_i$ and $B_i$.
--
--   This is the central combinatorial step: it lets one compare an agent's bundles across different score maximizers after one removal from each.
--
--   Differences from the source:
--   - generalization: α = α(w) for w ∈ Δ and prices p = p^λ(w) (Fix w, λ, ε) → arbitrary weights α ∈ ℝ^n and prices p ∈ ℝ^M; reason: the proof (pp. 17-19) uses only that one α and one p are shared by all allocations compared; taking α = α(w), p = p^λ(w) gives the printed statement for R_{λ,ε}(w)
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: profiles indexed by ℓ ≥ 1, padded with zeros → `ProfilesInterlace`: profiles as functions of a 0-based index k = ℓ − 1, padded with zeros indefinitely; reason: the same inequalities for every ℓ ≥ 1
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 16 (PDF 18), Lemma 5

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_5 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (α : Fin n → ℝ) (p : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (A B : Allocation n m) (hA : A ∈ scoreMaximizers v α p ε)
    (hB : B ∈ scoreMaximizers v α p ε) (i : Fin n) :
    ProfilesInterlace p (bundle A i) (bundle B i) := by sorry

end BalancedFairAlloc.Existence
