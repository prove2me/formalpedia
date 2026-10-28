-- Prove2me | Theorems.Thm_ClosestString_PTAS_claim_3
-- name    : ClosestString.PTAS.claim_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:24.509976+00:00
-- url     : https://prove2.me/theorems/3771a0b7-9a4d-42f0-81d1-7a614e6edf5b
-- title:
--   Claim 3 — min{ρ₀ − 1, ρ₂ − ρ₃, …, ρ_r − ρ_{r+1}} ≤ 1/(2r−1)
-- statement:
--   Let $u_1,\dots,u_n$ be strings of one length, $c$ a string of that length and $d\ge0$ an integer with $d(u_i,c)\le d$ for every $i$, and let $r\ge1$. With $\rho_0d=\max_{i,j}d(u_i,u_j)$ and $\rho_kd=\min_{i_1,\dots,i_k}p_{i_1,\dots,i_k}$ as in Section 2 (index tuples with repetitions),
--
--   $$\min\{\rho_0-1,\ \rho_2-\rho_3,\ \rho_3-\rho_4,\ \dots,\ \rho_r-\rho_{r+1}\}\ \le\ \frac1{2r-1},$$
--
--   that is, $\rho_0d-d\le d/(2r-1)$, or $\rho_kd-\rho_{k+1}d\le d/(2r-1)$ for some $2\le k\le r$.
--
--   Together with Claim 2 it proves Lemma 1: when $\rho_0>1+1/(2r-1)$ the first alternative is excluded.
--
--   Differences from the source:
--
--   - reading: Section 2 defines Q_{i1,…,ik} for "k distinct numbers" → index tuples idx : Fin k → Fin n with repetitions allowed; reason: Lemma 1's own statement does not require distinct indices and Figure 3 allows repeats; with distinct indices Claim 3 needs ρ_{r+1}, which does not exist when n < r + 1 (never excluded)
--   - generalization: s is the optimal Closest String center and d_opt = max_i d(s_i, s) → any center c and any d with d(u_i, c) ≤ d for all i; reason: the proof uses only the radius bound; c = s, d = d_opt is the paper's case, and Theorem 9 applies the result with u = t (p. 9)
--   - encoding: ratios ρ₀ = max d(s_i,s_j)/d_opt and ρ_k = min p/d_opt → the inequality multiplied by d: maxPairDist − d ≤ d/(2r−1) or minMismatch k − minMismatch (k+1) ≤ d/(2r−1), in ℝ; the minimum written as a disjunction; reason: avoids dividing by d_opt, which may be 0; equivalent whenever d_opt > 0
--   - reading: r, "the constant in the algorithm" → any integer r ≥ 1; reason: 1/(2r−1) needs r ≥ 1; the paper's r ≥ 2 is included
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 4, Claim 3

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

/-- **Claim 3** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 4), multiplied out by `d`, for any strings
`u_1, …, u_n` of one length, any center `c` with `d(u_i, c) ≤ d` for all `i`, and `r ≥ 1`:
`min{ρ₀ − 1, ρ₂ − ρ₃, …, ρ_r − ρ_{r+1}} ≤ 1/(2r−1)`, i.e.
`max_{i,j} d(u_i, u_j) − d ≤ d/(2r−1)` or some `2 ≤ k ≤ r` has
`ρ_k d − ρ_{k+1} d ≤ d/(2r−1)`. -/
theorem claim_3 {A : Type*} [DecidableEq A] {n m : ℕ} (u : Fin n → Fin m → A) (c : Fin m → A)
    (d : ℕ) (hd : ∀ i, hammingDist (u i) c ≤ d) (r : ℕ) (hr : 1 ≤ r) :
    (maxPairDist u : ℝ) - d ≤ d / (2 * (r : ℝ) - 1) ∨
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ r ∧
        (minMismatch u c k : ℝ) - minMismatch u c (k + 1) ≤ d / (2 * (r : ℝ) - 1) := by sorry

end ClosestString.PTAS
