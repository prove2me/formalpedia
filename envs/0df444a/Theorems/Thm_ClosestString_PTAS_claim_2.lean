-- Prove2me | Theorems.Thm_ClosestString_PTAS_claim_2
-- name    : ClosestString.PTAS.claim_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:15.902245+00:00
-- url     : https://prove2.me/theorems/45e19f74-6f5b-467c-a3dd-0e4d9dfc753b
-- title:
--   Claim 2 (corrected: indices range over 1..n) — an r-tuple whose agreement set has at most (ρ_k − ρ_{k+1})d positions where s_{i1} differs from both s_l and the center
-- statement:
--   Let $u_1,\dots,u_n$ ($n\ge1$) be strings of one length over an alphabet $\Sigma$ and $c$ a string of that length. For an index tuple $(i_1,\dots,i_k)$ (repetitions allowed) let $Q_{i_1,\dots,i_k}$ be the positions where $u_{i_1},\dots,u_{i_k}$ agree, $p_{i_1,\dots,i_k}$ the number of positions of $Q_{i_1,\dots,i_k}$ where $u_{i_1}$ differs from $c$, and $\rho_k d=\min_{i_1,\dots,i_k}p_{i_1,\dots,i_k}$.
--
--   Then for every $k$ with $2\le k\le r$ there are indices $1\le i_1,\dots,i_r\le n$ such that for every $1\le l\le n$,
--
--   $$\big|\{j\in Q_{i_1,\dots,i_r} : u_{i_1}[j]\ne u_l[j]\ \text{and}\ u_{i_1}[j]\ne c[j]\}\big|\ \le\ \rho_k d-\rho_{k+1}d.$$
--
--   This is the first step of the proof of Lemma 1: combined with Claim 3 it produces the $r$ strings whose common letters approximate the center.
--
--   Differences from the source:
--
--   - correction: indices 1 ≤ i1, …, ir ≤ m (statement and proof) → indices in Fin n (1 ≤ i_j ≤ n); reason: the i_j index strings, of which there are n; read with ≤ m (and tuples as in the next line) the claim is false: Σ = {a,b}, n = 2, m = 1, s1 = a, s2 = b, s = b, r = k = 2 gives ρ2 d = ρ3 d = 0 but the only allowed tuple (1,1) has a position with s1 ≠ s2 and s1 ≠ s
--   - reading: Section 2 defines Q_{i1,…,ik} for "k distinct numbers" → index tuples idx : Fin k → Fin n with repetitions allowed; reason: Lemma 1's own statement does not require distinct indices and Figure 3 allows repeats; with distinct indices Claim 3 needs ρ_{r+1}, which does not exist when n < r + 1 (never excluded)
--   - generalization: s is the optimal Closest String center with radius d_opt → any center c (no radius hypothesis); reason: the proof uses no property of s; c = s is the paper's case
--   - encoding: ratios ρ₀ = max d(s_i,s_j)/d_opt and ρ_k = min p/d_opt → the same quantities multiplied by d (maxPairDist, minMismatch), in ℝ or ℤ; reason: avoids dividing by d_opt, which may be 0; equivalent whenever d_opt > 0
--   - encoding: positions 1..m, indices 1..n, s_{i1} → 0-based Fin m, Fin n; s_{i1} is u (idx 0); reason: relabelling; changes no instance
--   - encoding: a set S = {s1, …, sn} of strings → n ≥ 1 ([NeZero n]); reason: the instance has at least one string; with n = 0 no index tuple exists
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 4, Claim 2

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

/-- **Claim 2** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 4), multiplied out by `d_opt`, for any
`n ≥ 1` strings `u` of one length, any center `c`, index tuples with repetitions allowed, and the
index range corrected to `1 ≤ i_j ≤ n`: for `2 ≤ k ≤ r` there is an `r`-tuple `idx` such that for
every `l`, the number of positions `j ∈ Q_idx` with `u_{idx 0}[j] ≠ u_l[j]` and `u_{idx 0}[j] ≠ c[j]`
is at most `ρ_k d_opt − ρ_{k+1} d_opt = minMismatch u c k − minMismatch u c (k+1)`. -/
theorem claim_2 {A : Type*} [DecidableEq A] {n m : ℕ} [NeZero n] (u : Fin n → Fin m → A)
    (c : Fin m → A) (r k : ℕ) (hk : 2 ≤ k) (hkr : k ≤ r) :
    ∃ idx : Fin r → Fin n, ∀ l : Fin n,
      (((agreeSet u idx).filter (fun j =>
          u (idx ⟨0, by omega⟩) j ≠ u l j ∧ u (idx ⟨0, by omega⟩) j ≠ c j)).card : ℤ)
        ≤ (minMismatch u c k : ℤ) - minMismatch u c (k + 1) := by sorry

end ClosestString.PTAS
