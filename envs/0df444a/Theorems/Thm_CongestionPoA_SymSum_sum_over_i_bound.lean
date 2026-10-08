-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_sum_over_i_bound
-- name    : CongestionPoA.SymSum.sum_over_i_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:51:13.928781+00:00
-- url     : https://prove2.me/theorems/94227458-2ebc-4fe5-817d-631075afa2f9
-- title:
--   Theorem 3, proof — summing over $i$: a bound on $\mathrm{SUM}(A)$
-- statement:
--   Let $G$ be a symmetric congestion game with $N\ge1$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$; let $A$ be a pure Nash equilibrium and $P$ any pure strategy profile. Then
--   $$\mathrm{SUM}(A)\le \frac{N-1}{N}\sum_{e\in E}a_e\bigl(n_e(P)n_e(A)+n_e(P)\bigr)+\frac1N\sum_{e\in E}a_e\,n_e(P)+\sum_{e\in E}b_e\,n_e(P).$$
--   For identity latencies this is the paper's $\mathrm{SUM}(A)\le\frac{N-1}{N}\sum_e(n_e(P)n_e(A)+n_e(P))+\frac1N\sum_e n_e(P)$.
--
--   It follows by adding the previous bound over all players $i$, and it is the form to which Lemma 1 is applied facility by facility.
--
--   **Formalization Note** The coefficients are explicit parameters; the fractions are real numbers.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 4, Theorem 3, proof (third display)

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 4, unnumbered step of the proof of Theorem 3: summing over all `i ∈ N` bounds the social
cost of the Nash equilibrium,
`SUM(A) ≤ ((N − 1)/N) Σ_{e∈E} (n_e(P)n_e(A) + n_e(P)) + (1/N) Σ_{e∈E} n_e(P)`.

**Formalization Note.** Printed for identity latencies; for linear latencies `f_e(k) = a_e k + b_e`
(`a_e, b_e ≥ 0`, explicit binders) the bound reads
`SUM(A) ≤ ((N−1)/N) Σ_e a_e(n_e(P)n_e(A) + n_e(P)) + (1/N) Σ_e a_e n_e(P) + Σ_e b_e n_e(P)`, the printed
one when `a_e = 1`, `b_e = 0`. The paper has `N ≥ 1` players (`N = {1, …, n}`); the hypothesis
`1 ≤ N` is stated and the fractions are computed in `ℝ`. `P` is any pure strategy profile. -/
theorem sum_over_i_bound {N : ℕ} (hN : 1 ≤ N) {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    CongestionPoA.AsymSum.sumCost G A ≤
      ((N : ℝ) - 1) / N * ∑ e, a e * ((CongestionPoA.AsymSum.load P e : ℝ) * (CongestionPoA.AsymSum.load A e : ℝ) + (CongestionPoA.AsymSum.load P e : ℝ))
        + 1 / (N : ℝ) * ∑ e, a e * (CongestionPoA.AsymSum.load P e : ℝ) + ∑ e, b e * (CongestionPoA.AsymSum.load P e : ℝ) := by sorry

end CongestionPoA.SymSum
