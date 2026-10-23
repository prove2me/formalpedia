-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_bellman_4
-- name    : CorrClusterExp.IBR.bellman_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:12.516313+00:00
-- url     : https://prove2.me/theorems/4fbb06bd-12ee-45fa-ae30-5d5254ee10fc
-- title:
--   (4), §3.2, p. 16 — Bellman equation V_k = min_{h∈[k]} g_k(h) + V_{k−h} for the optimal IBR partition
-- statement:
--   Let $0<q\le\tfrac12$ and let $w_1\ge w_2\ge\dots\ge w_n\ge 0$ with $n\ge 1$. For $h\in[n]$ let $g_n(h)$ be the worst-case variance of a block made of the first $h$ clusters under the block law of Proposition 3.1, and let $V_{n-h}$ be the worst-case variance of the optimal IBR experiment on the remaining clusters $h+1,\dots,n$ ($V_0=0$). Then the worst-case variance $V_n=V^{\mathrm{DP}}$ of the optimal IBR experiment satisfies the Bellman equation
--   $$
--   V_n=\min_{h\in[n]}\ g_n(h)+V_{n-h}. \tag{4}
--   $$
--   Applied to the last $k$ clusters, this is the recursion $V_k=\min_{h\in[k]}g_k(h)+V_{k-h}$ of the paper, which computes the optimal partition in polynomial time.
--
--   **Formalization Note** The minimum is stated as two clauses: $V_n\le g_n(h)+V_{n-h}$ for every $h\in[n]$, and equality for some $h\in[n]$. The suffix sizes are `fun i : Fin (n - h) => w ⟨h + i, _⟩`.
--
--   Differences from the source:
--   - encoding: $V_k$ for the last $k$ of the $n$ sorted clusters → $V^{\mathrm{DP}}$ of the suffix size vector, with the equation stated for every $n$ and $w$; reason: the recursion at level $k$ is the instance on the suffix, so every level is covered.
--   - encoding: $\min_{h\in[k]}$ → "$\le$ for all $h\in[1,n]$ and $=$ for some"; reason: same statement for a finite nonempty index set.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 16, §3.2, equation (4)

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

open Matrix Finset

theorem bellman_4 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 1 ≤ n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) :
    (∀ (h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ n),
      VDP q w ≤ worstCase (corr q (fracLaw q h)) (fun i : Fin h => w (Fin.castLE h2 i)) +
        VDP q (fun i : Fin (n - h) => w ⟨h + i.val, by have := i.isLt; omega⟩)) ∧
    ∃ (h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ n),
      VDP q w = worstCase (corr q (fracLaw q h)) (fun i : Fin h => w (Fin.castLE h2 i)) +
        VDP q (fun i : Fin (n - h) => w ⟨h + i.val, by have := i.isLt; omega⟩) := by sorry

end CorrClusterExp.IBR
