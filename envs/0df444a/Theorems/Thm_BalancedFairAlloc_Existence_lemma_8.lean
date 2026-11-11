-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_8
-- name    : BalancedFairAlloc.Existence.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:48.711638+00:00
-- url     : https://prove2.me/theorems/251b9956-4caf-494b-9982-90cfed8285ae
-- title:
--   Lemma 8 — applying KKM: a common point w* with a minimum-label witness for every agent
-- statement:
--   Assume $n\ge2$, $r\ge1$, $V=\max_{i,g}|v_{ig}|$, $M_0=4V+1$, $H=2(r+2)V$, $K=2(r+1)V$, $\gamma>0$ and $\rho$ as in (24). Then there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every price map $w\mapsto p(w)$ that is continuous on $\Delta$ with $|p(w)_g|\le M_0$ there are $w^*\in\Delta$ and allocations $B^1,\dots,B^n\in R(\alpha(w^*),p(w^*),\varepsilon)$ such that, for every agent $i$,
--
--   $$d_i(B^i,w^*)=\min_{j\in N}d_j(B^i,w^*).$$
--
--   With $p=p^\lambda$ this is Lemma 8 for $R_{\lambda,\varepsilon}(w^*)$, for every $\lambda>0$.
--
--   Differences from the source:
--   - reading: Lemma 8 under the standing choices of p. 21 (ρ as in (24); ε small enough for Lemma 7; λ > 0) → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), ∀ price maps; reason: the proof invokes Lemma 7 'once ε is small enough'; the same explicit form as Lemma 7
--   - generalization: prices p^λ(w) → every price map continuous on Δ with |p(w)_g| ≤ M₀; reason: p^λ is continuous by Lemma 3 and lies in the box of (10); the statement specializes to every λ > 0
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: H, K, V as in Lemma 7 → real variables with defining equations, V = `vmax v`; reason: same numbers
--   - encoding: allocations B^1, …, B^n → a family B : Fin n → Allocation n m; reason: one witness per agent
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 21 (PDF 23), Lemma 8

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_8 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (H K : ℝ) (hH : H = 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v)
    (hK : K = 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v)
    (γ ρ : ℝ) (hγ : 0 < γ) (hρ0 : 0 < ρ)
    (hρ : ρ < γ / (2 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ pmap : (Fin n → ℝ) → Fin m → ℝ, ContinuousOn pmap (stdSimplex ℝ (Fin n)) →
        (∀ w ∈ stdSimplex ℝ (Fin n), ∀ g, |pmap w g| ≤ M0 v) →
        ∃ w ∈ stdSimplex ℝ (Fin n), ∃ B : Fin n → Allocation n m, ∀ i,
          B i ∈ scoreMaximizers v (alphaW ρ w) (pmap w) ε ∧
          ∀ j, label v γ (alphaW ρ w) (B i) i ≤ label v γ (alphaW ρ w) (B i) j := by sorry

end BalancedFairAlloc.Existence
