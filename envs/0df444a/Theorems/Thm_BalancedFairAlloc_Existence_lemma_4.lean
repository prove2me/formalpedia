-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_4
-- name    : BalancedFairAlloc.Existence.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:50.092233+00:00
-- url     : https://prove2.me/theorems/7c9073a1-4f7f-4bad-aabb-c21e9df3aa09
-- title:
--   Lemma 4 — the dual (6) has an optimal solution with |ξ_i| ≤ 2V and |p_g| ≤ 3V
-- statement:
--   Assume the standing assumptions of Section 3: $n\ge2$ agents and $r=\lfloor m/n\rfloor\ge1$; let $V=\max_{i,g}|v_{ig}|$, $\rho\in(0,1/n)$, and for $w\in\Delta$ let $\alpha_i(w)=\rho+(1-n\rho)w_i$. Then the dual LP (6),
--
--   $$\min_{\xi,p}\ \Psi(\xi,p)=\sum_gp_g+r\sum_i\xi_i+\sum_i(\xi_i)_+\quad\text{s.t.}\quad\xi_i+p_g\ge\alpha_i(w)v_{ig}\ \ \forall i,g,$$
--
--   has an optimal solution $(\xi,p)$ with $|\xi_i|\le2V$ for every agent and $|p_g|\le3V$ for every item.
--
--   The bound places an exact dual optimum in the box $[-M_0,M_0]^{n+m}$, $M_0=4V+1$, used to regularize the dual in (10).
--
--   Differences from the source:
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: ρ ∈ (0, 1/n) fixed on p. 13 → explicit hypotheses `0 < ρ` and `ρ < 1 / n`; reason: the weights α(w) of eq. (4) are defined under this choice
--   - encoding: V := max_{i,g} |v_ig| → `vmax v`; reason: same number
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 14 (PDF 16), Lemma 4

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

theorem lemma_4 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / (n : ℝ))
    (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n)) :
    ∃ (ξ : Fin n → ℝ) (p : Fin m → ℝ), IsDualOptimal v (alphaW ρ w) ξ p ∧
      (∀ i, |ξ i| ≤ 2 * vmax v) ∧ (∀ g, |p g| ≤ 3 * vmax v) := by sorry

end BalancedFairAlloc.Existence
