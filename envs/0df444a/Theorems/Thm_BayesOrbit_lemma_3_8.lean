-- Prove2me | Theorems.Thm_BayesOrbit_lemma_3_8
-- name    : BayesOrbit.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:26.099839+00:00
-- url     : https://prove2.me/theorems/fcaf24c3-c52d-42e3-ba76-aea3110fcb09
-- title:
--   Lemma 3.8 — a single integer scale $d$ and integer exponents approximate any positive vector
-- statement:
--   Let $K$ and $M$ be finite sets with $|K|\le|M|$, and let $(r_k[m])_{k\in K,m\in M}$ be positive reals such that the numbers $\ln r_k[m]$ are algebraically independent over $\mathbb Q$. Given positive reals $(\gamma_k)_{k\in K}$ and $\varepsilon>0$, there are integers $(u_m)_{m\in M}$ and one integer $d$ such that for all $k\in K$
--   $$
--   (1-\varepsilon)\,\gamma_k\,e^{d}\le\prod_m r_k[m]^{u_m}\le(1+\varepsilon)\,\gamma_k\,e^{d}.\tag{3.11}
--   $$
--
--   This is the approximation step of the main theorem: the common factor $e^d$ disappears when a posterior is normalized, so only the ratios of the $\gamma_k$ matter. Rows are not assumed to sum to one.
--
--   Differences from the source:
--   - encoding: γ_1, …, γ_k and u_1, …, u_m, with k and m used as cardinalities → γ : K → ℝ and u : M → ℤ; reason: the printed indices abuse k and m; same data
-- source:
--   Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted manuscript (Enlighten 227272), Lemma 3.8, eq. (3.11), p.16

import Mathlib

open scoped BigOperators

namespace BayesOrbit

/-- Lemma 3.8 of Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted
manuscript (Enlighten 227272), p.16 (PDF 17), eq. (3.11), as printed.

**Formalization Note.** `r` is any positive matrix: the lemma does not assume rows summing to `1`.
Algebraic independence is over `ℚ`, of the family indexed by `K × M`. The exponents `u m` and the
scale `d` are integers (`zpow`, and `Real.exp` at the cast of `d`), `d` is one integer for all `k`,
and `ε > 0` has no upper bound. -/
theorem lemma_3_8 {K M : Type*} [Fintype K] [Fintype M] (r : K → M → ℝ) (hr : ∀ k m, 0 < r k m)
    (hind : AlgebraicIndependent ℚ (fun x : K × M => Real.log (r x.1 x.2)))
    (hcard : Fintype.card K ≤ Fintype.card M)
    (γ : K → ℝ) (hγ : ∀ k, 0 < γ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : M → ℤ) (d : ℤ), ∀ k,
      (1 - ε) * γ k * Real.exp (d : ℝ) ≤ ∏ m, r k m ^ u m ∧
      ∏ m, r k m ^ u m ≤ (1 + ε) * γ k * Real.exp (d : ℝ) := by sorry

end BayesOrbit
