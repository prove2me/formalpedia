-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_11
-- name    : BalancedFairAlloc.Existence.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:48.088884+00:00
-- url     : https://prove2.me/theorems/5bcd67b5-1166-4849-9a13-0bfd87f3ac87
-- title:
--   Lemma 11 — consolidating the witnesses: some witness has f_ij ≤ γ for all i, j
-- statement:
--   Assume $n\ge2$, $r\ge1$, $\gamma>0$ and weights $\alpha_i>0$. Let $B^1,\dots,B^n$ be allocations such that agent $i$ has minimum label in $B^i$: $d_i(B^i)=\min_jd_j(B^i)$, with the labels (22) computed from the flows $F_{ij}=[\alpha_if_{ij}+\gamma(\alpha_j-\alpha_i)]_+$. If numbers $\beta_1,\dots,\beta_n$ satisfy $\alpha_if_{ij}(X)\le\beta_j-\beta_i$ for every witness $X\in\{B^1,\dots,B^n\}$ and all $i,j\in N$, then some witness $A$ satisfies
--
--   $$f_{ij}(A)\le\gamma\qquad\text{for all }i,j\in N.$$
--
--   Differences from the source:
--   - generalization: labels at w* with the limiting weights α(w*), witnesses B^i ∈ R_{λ,ε}(w*) in the limit → any weights α with α_i > 0 and any allocations B^i with the minimum-label property; reason: the proof uses only α_i > 0 and the minimum-label inequalities; α(w*) has α_i ≥ ρ > 0
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: d_i(B^i, w*) = min_j d_j(B^i, w*) → `label v γ α (B i) i ≤ label v γ α (B i) j` for all j; reason: same condition
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 24 (PDF 26), Lemma 11

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_11 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (B : Fin n → Allocation n m)
    (hmin : ∀ i j, label v γ α (B i) i ≤ label v γ α (B i) j)
    (β : Fin n → ℝ) (hβ : ∀ k i j, α i * residualEnvy v (B k) i j ≤ β j - β i) :
    ∃ k, ∀ i j, residualEnvy v (B k) i j ≤ γ := by sorry

end BalancedFairAlloc.Existence
