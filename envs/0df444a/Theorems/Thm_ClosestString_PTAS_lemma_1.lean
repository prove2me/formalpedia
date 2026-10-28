-- Prove2me | Theorems.Thm_ClosestString_PTAS_lemma_1
-- name    : ClosestString.PTAS.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:15.371787+00:00
-- url     : https://prove2.me/theorems/9e033499-c7f5-46bf-b0fb-c8dee70c02fd
-- title:
--   Lemma 1 — if ρ₀ > 1 + 1/(2r−1), some r-tuple's agreement set Q has d^Q(s_l, s_{i1}) − d^Q(s_l, s) ≤ d_opt/(2r−1) for every l
-- statement:
--   Let $u_1,\dots,u_n$ be strings of one length, $c$ a string of that length (the center) and $d\ge0$ an integer with $d(u_i,c)\le d$ for every $i$, and let $r\ge1$. Write $\rho_0d=\max_{i,j}d(u_i,u_j)$ and, for indices $i_1,\dots,i_r$ (repetitions allowed), $Q=Q_{i_1,\dots,i_r}$ for the positions where $u_{i_1},\dots,u_{i_r}$ agree. If
--
--   $$\max_{i,j}d(u_i,u_j)\ >\ \Big(1+\frac1{2r-1}\Big)d,$$
--
--   then there are indices $1\le i_1,\dots,i_r\le n$ such that for every $1\le l\le n$
--
--   $$d(u_l|_Q,u_{i_1}|_Q)-d(u_l|_Q,c|_Q)\ \le\ \frac1{2r-1}\,d.$$
--
--   This is the key lemma of the paper: on the agreement set of a well-chosen $r$-tuple, the common letters are almost as good as the optimal center. Theorem 9 applies it with $u_i=t_i$, the substrings closest to an optimal center (Fact 1, p. 10).
--
--   Differences from the source:
--
--   - reading: Section 2 defines Q_{i1,…,ik} for "k distinct numbers" → index tuples idx : Fin k → Fin n with repetitions allowed; reason: Lemma 1's own statement does not require distinct indices and Figure 3 allows repeats; with distinct indices Claim 3 needs ρ_{r+1}, which does not exist when n < r + 1 (never excluded)
--   - generalization: s is the optimal Closest String center and d_opt = max_i d(s_i, s) → any center c and any d with d(u_i, c) ≤ d for all i; reason: the proof uses only the radius bound; c = s, d = d_opt is the paper's case, and Theorem 9 applies the result with u = t (p. 9)
--   - encoding: ratios ρ₀ = max d(s_i,s_j)/d_opt and ρ_k = min p/d_opt → hypothesis (1 + 1/(2r−1))·d < maxPairDist u and conclusion with d/(2r−1), in ℝ; reason: avoids dividing by d_opt, which may be 0; equivalent whenever d_opt > 0
--   - reading: "for any constant r" → any integer r ≥ 1; reason: 1/(2r−1) needs r ≥ 1; for r = 1 the hypothesis cannot hold (ρ₀ ≤ 2 by the triangle inequality), as in the paper
--   - encoding: positions 1..m, indices 1..n, s_{i1} → 0-based Fin m, Fin n; s_{i1} is u (idx 0); reason: relabelling; changes no instance
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 3, Lemma 1 (proof pp. 3–4)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

/-- **Lemma 1** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 3), multiplied out by `d`, for any strings
`u_1, …, u_n` of one length `m'`, any center `c` with `d(u_i, c) ≤ d` for all `i`, any `r ≥ 1`, and
index tuples with repetitions allowed: if `max_{i,j} d(u_i, u_j) > (1 + 1/(2r−1)) d` (i.e.
`ρ₀ > 1 + 1/(2r−1)`), there is an `r`-tuple `idx` with
`d^Q(u_l, u_{idx 0}) − d^Q(u_l, c) ≤ d/(2r−1)` for every `l`, where `Q = Q_idx`. -/
theorem lemma_1 {A : Type*} [DecidableEq A] {n m' : ℕ} (u : Fin n → Fin m' → A) (c : Fin m' → A)
    (d : ℕ) (hd : ∀ i, hammingDist (u i) c ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (hρ : (1 + 1 / (2 * (r : ℝ) - 1)) * d < maxPairDist u) :
    ∃ idx : Fin r → Fin n, ∀ l : Fin n,
      (distOn (agreeSet u idx) (u l) (u (idx ⟨0, by omega⟩)) : ℝ)
        - distOn (agreeSet u idx) (u l) c ≤ d / (2 * (r : ℝ) - 1) := by sorry

end ClosestString.PTAS
