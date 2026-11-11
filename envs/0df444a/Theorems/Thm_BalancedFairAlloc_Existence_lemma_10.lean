-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_10
-- name    : BalancedFairAlloc.Existence.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:47.195459+00:00
-- url     : https://prove2.me/theorems/fd5648d0-8b7c-4d41-97a7-35a6b2281b0d
-- title:
--   Lemma 10 — residual envy is bounded by the price gap: α_i f_ij(X) ≤ L_j(X) − U_i(X)
-- statement:
--   Work in the context of §3.6, made explicit: $n\ge2$, $r\ge1$; weights $\alpha_i>0$; a dual-feasible $(\xi,p)$ for (6) with these weights; a family $B^1,\dots,B^n$ of balanced allocations such that every assigned pair is tight ($\xi_i+p_g=\alpha_iv_{ig}$ for $g\in B^k_i$) and eq. (9) holds for every witness. Then for every witness $X$ and all agents $i,j$,
--
--   $$\alpha_i\,f_{ij}(X)\le L_j(X)-U_i(X),$$
--
--   with $f_{ij}$ the residual envy (20) and $L_j,U_i$ from (26).
--
--   Combined with Lemma 9, it gives $\alpha_if_{ij}(X)\le\beta_j-\beta_i$ on every witness, the hypothesis of Lemma 11.
--
--   Differences from the source:
--   - reading: §3.6's context: α, ξ, p the limiting weights and exact optimal dual at w*, B = {B^1, …, B^n} the witness family, assigned pairs tight, dual feasibility, eq. (9) for every witness, interlacing for the limits → explicit hypotheses: α_i > 0; (ξ, p) dual feasible for (6) with weights α; B : Fin n → Allocation n m with every B k balanced; ξ_i + p_g = α_i v_ig for g ∈ (B k)_i; eq. (9) for every witness; reason: the lemma is stated in this context (p. 22), which the BRIEF's standing assumption 6 records
--   - generalization: α = α(w*) ∈ Δ with α_i ≥ ρ; witnesses with interlacing price profiles and the minimum-label property → any α with α_i > 0; no interlacing or minimum-label hypothesis; reason: the proof (pp. 23-24) uses only dual feasibility, tightness, eq. (9) and α_i > 0; the paper's witnesses satisfy these
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 23 (PDF 25), Lemma 10 (context p. 22, PDF 24)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_10 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) (ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (hfeas : IsDualFeasible v α ξ p)
    (B : Fin n → Allocation n m) (hbal : ∀ k, IsBalanced (B k))
    (htight : ∀ k i, ∀ g ∈ bundle (B k) i, ξ i + p g = α i * v i g)
    (hslack : ∀ k i, ((bundle (B k) i).card = m / n → ξ i ≤ 0) ∧
      ((bundle (B k) i).card = m / n + 1 → 0 ≤ ξ i)) :
    ∀ k i j, α i * residualEnvy v (B k) i j ≤ priceL p (B k) j - priceU p ξ (B k) i := by sorry

end BalancedFairAlloc.Existence
