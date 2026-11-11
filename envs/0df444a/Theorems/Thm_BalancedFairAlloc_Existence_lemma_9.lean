-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_9
-- name    : BalancedFairAlloc.Existence.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:50.338602+00:00
-- url     : https://prove2.me/theorems/c1a2bef9-3e7b-426e-aa3c-6c0ae027969f
-- title:
--   Lemma 9 — common price intervals: for each agent some β_i lies between L_i(X) and U_i(X) on every witness
-- statement:
--   Work in the context of §3.6, made explicit: $n\ge2$, $r\ge1$; weights $\alpha_i>0$; a dual-feasible $(\xi,p)$ for (6) with these weights ($\xi_i+p_g\ge\alpha_iv_{ig}$); a family $B^1,\dots,B^n$ of balanced allocations (the witnesses) such that every assigned pair is tight ($\xi_i+p_g=\alpha_iv_{ig}$ for $g\in B^k_i$), eq. (9) holds for every witness ($|B^k_i|=r\Rightarrow\xi_i\le0$ and $|B^k_i|=r+1\Rightarrow\xi_i\ge0$), and for every agent $i$ the price profiles of $B^k_i$ and $B^l_i$ interlace as in Lemma 5, for all $k,l$. Then for every agent $i$ there is a number $\beta_i$ with
--
--   $$L_i(X)\le\beta_i\le U_i(X)\qquad\text{for every witness }X\in\{B^1,\dots,B^n\},$$
--
--   where $L_i$ and $U_i$ are defined in (26).
--
--   Differences from the source:
--   - reading: §3.6's context: α, ξ, p the limiting weights and exact optimal dual at w*, B = {B^1, …, B^n} the witness family, assigned pairs tight, dual feasibility, eq. (9) for every witness, interlacing for the limits → explicit hypotheses: α_i > 0; (ξ, p) dual feasible for (6) with weights α; B : Fin n → Allocation n m with every B k balanced; ξ_i + p_g = α_i v_ig for g ∈ (B k)_i; eq. (9) for every witness; reason: the lemma is stated in this context (p. 22), which the BRIEF's standing assumption 6 records
--   - generalization: α = α(w*) ∈ Δ with α_i ≥ ρ; witnesses in the limit of score maximizers with the minimum-label property → any α with α_i > 0; witnesses need not satisfy the minimum-label inequalities; reason: the proof uses only the listed hypotheses; the paper's limiting objects satisfy them (welfare maximization and exact dual optimality follow from feasibility, tightness and (9))
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: interlacing for the limits → `ProfilesInterlace p (bundle (B k) i) (bundle (B l) i)` for all k, l, i; reason: the conclusion of Lemma 5 passed to the limit, as stated on p. 22
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 23 (PDF 25), Lemma 9 (context p. 22, PDF 24)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_9 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) (ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (hfeas : IsDualFeasible v α ξ p)
    (B : Fin n → Allocation n m) (hbal : ∀ k, IsBalanced (B k))
    (htight : ∀ k i, ∀ g ∈ bundle (B k) i, ξ i + p g = α i * v i g)
    (hslack : ∀ k i, ((bundle (B k) i).card = m / n → ξ i ≤ 0) ∧
      ((bundle (B k) i).card = m / n + 1 → 0 ≤ ξ i))
    (hinterlace : ∀ k l i, ProfilesInterlace p (bundle (B k) i) (bundle (B l) i)) :
    ∀ i, ∃ β : ℝ, ∀ k, priceL p (B k) i ≤ β ∧ β ≤ priceU p ξ (B k) i := by sorry

end BalancedFairAlloc.Existence
