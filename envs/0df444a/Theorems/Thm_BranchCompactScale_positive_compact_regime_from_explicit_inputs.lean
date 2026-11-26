-- Prove2me | Theorems.Thm_BranchCompactScale_positive_compact_regime_from_explicit_inputs
-- name    : BranchCompactScale.positive_compact_regime_from_explicit_inputs
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:11:58.611472+00:00
-- url     : https://prove2.me/theorems/e68fdb1a-1bc7-45a0-8941-6a0df1aeb285
-- title:
--   Compact scale: eventual strict positivity from a verified low-height range and explicit zero counts
-- statement:
--   Let $(\gamma_i,\varepsilon_i)_{i\in I}$ satisfy $\gamma_i\ge2$ and $|\varepsilon_i|\le1/2$. Assume that $\varepsilon_i=0$ whenever $\gamma_i\le1000$, and that at least one index has $\gamma_i\le100$. Write
--   $$a_i=\gamma_i^2-\varepsilon_i^2,\quad b_i=2\varepsilon_i\gamma_i,\quad B_i=a_i-ib_i.$$
--   Assume $\sum_i a_i^{-1}<\infty$ and that every finite set of indices in $T\le\gamma_i<T+1$ has cardinality at most $50\log(T+3)$ for $T\ge1000$; multiplicities are counted by the index set. If $k_j\to\infty$ through natural numbers and $\lambda_j\to L>0$, then
--   $$\operatorname{Re}\sum_i\left(1+\frac{\lambda_jB_i}{k_j}\right)^{-k_j}>0$$
--   for all sufficiently large $j$. The assumptions are explicit analytic inputs, and the conclusion allows either finitely or infinitely many indices with nonzero displacement.
-- source:
--   Desenvolvimento RH, On the Infinitude of Off-Critical Zeros, Section 6 compact-scale obstruction, repaired and formalized 2026-11-18. New negative-atom comparison, explicit unit-shell reciprocal-square estimate and moving-scale dominated-convergence proof. Mathlib standard analysis at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
open Set Filter Topology

theorem BranchCompactScale.positive_compact_regime_from_explicit_inputs {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    ∀ᶠ j : ℕ in atTop, 0 <
      (∑' i, ((1+(lam j : ℂ)*
        ((((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I)/(k j : ℂ))⁻¹)^(k j)).re := by sorry
