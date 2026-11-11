-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_7
-- name    : BalancedFairAlloc.Existence.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:29.125085+00:00
-- url     : https://prove2.me/theorems/e1353f0c-ea04-4073-9b8f-68ed9222aee9
-- title:
--   Lemma 7 — with ρ below the threshold (24), for all small ε the label sets satisfy the KKM face condition
-- statement:
--   Assume $n\ge2$, $r\ge1$, let $V=\max_{i,g}|v_{ig}|$, $M_0=4V+1$, $H=2(r+2)V$, $K=2(r+1)V$, $\gamma>0$, and
--
--   $$0<\rho<\frac{\gamma}{2n\big(\gamma+H+(n-1)K\big)}.\tag{24}$$
--
--   Then there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every price map $w\mapsto p(w)$ with $|p(w)_g|\le M_0$ for all $w\in\Delta$ and all items $g$, the label sets $F_i$ (eq. (23) with prices $p(w)$) satisfy the KKM face condition: for every nonempty $T\subseteq N$,
--
--   $$\Delta(T)=\{w\in\Delta: w_i=0\ \forall i\notin T\}\subseteq\bigcup_{i\in T}F_i.$$
--
--   With $p=p^\lambda$ for each $\lambda>0$ this is Lemma 7: one $\varepsilon_0$ works for every $\lambda$.
--
--   Differences from the source:
--   - reading: for all sufficiently small ε > 0 and every λ > 0 → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), ∀ price maps (standing for all λ > 0); reason: ε₀ may depend on the instance, γ and ρ but not on λ or w, as the proof's bound (25) shows
--   - generalization: prices p^λ(w) for every λ > 0 → every price map with |p(w)_g| ≤ M₀ on Δ (no continuity required); reason: p^λ(w) lies in the box [−M₀, M₀] of (10), which is all the proof uses (through C_Φ = nM₀(r+1)(r+2)); the statement specializes to every λ
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: H := 2(r+2)V, K := 2(r+1)V with V = max |v_ig| → real variables H, K with defining equations, V = `vmax v`, r = `m / n` cast to ℝ; reason: same numbers
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 21 (PDF 23), Lemma 7

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_7 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (H K : ℝ) (hH : H = 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v)
    (hK : K = 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v)
    (γ ρ : ℝ) (hγ : 0 < γ) (hρ0 : 0 < ρ)
    (hρ : ρ < γ / (2 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ pmap : (Fin n → ℝ) → Fin m → ℝ,
        (∀ w ∈ stdSimplex ℝ (Fin n), ∀ g, |pmap w g| ≤ M0 v) →
        ∀ T : Finset (Fin n), T.Nonempty →
          simplexFace T ⊆ ⋃ i ∈ T, labelSet v ρ γ ε pmap i := by sorry

end BalancedFairAlloc.Existence
