-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_7
-- name    : AdWordsMSVV.Tradeoff.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:18.069081+00:00
-- url     : https://prove2.me/theorems/45f7f06e-2088-4403-aea9-2bebf1d5ec78
-- title:
--   Lemma 7, p. 11 — Σ_{i=1}^{k−1} ψ(i)(α_i − β_i) ≤ N/k
-- statement:
--   Fix $k\ge1$, an adwords instance with $N$ bidders, unit budgets and nonnegative bids $c_{b,t}$, a monotonically decreasing tradeoff function $\psi:\{1,\dots,k\}\to\mathbb R_{\ge0}$ with $\psi(k)=0$, a run $\sigma$ of the discrete algorithm with tradeoff function $\psi$, and any allocation $\tau$. For $1\le i\le k-1$ let
--   $$\alpha_i=\sum_{q:\ \mathrm{type}(q)=i}\mathrm{OPT}(q),\qquad \beta_i=\sum_{q:\ \mathrm{slab}(q)=i}\mathrm{ALG}(q),$$
--   where $\mathrm{OPT}(q)$ is the bid of the bidder $\tau$ assigns $q$ to, $\mathrm{type}(q)$ is that bidder's type at the end of the run, and $\mathrm{ALG}(q)$, $\mathrm{slab}(q)$ are as in Lemma 6. Then
--   $$\sum_{i=1}^{k-1}\psi(i)(\alpha_i-\beta_i)\le\frac Nk .$$
--
--   Applied to Theorem 8's $\psi_k(i)=\sum_{j=i}^{k-1}y^*_j$ (which satisfies these hypotheses), through $\Delta\cdot y^*=\sum_i(\alpha_i-\beta_i)\psi_k(i)$ this is the bound on the error term in the proof of Theorem 8.
--
--   **Formalization Note** The two sums are the paper's opening observations in the proof of Lemma 7, taken here as the definitions of $\alpha_i$ and $\beta_i$. The paper states the lemma for a generic monotonically decreasing $\psi:[1\dots k]\to\mathbb R^+$; the added hypothesis $\psi(k)=0$ (true for Theorem 8's $\psi_k$ and for §3's $\psi_k$) replaces the paper's bound on the slab-$k$ term, which rests on its simplifying assumption that bidders of type $j$ spend exactly $j/k$: for a tradeoff function positive at slab $k$ the slab-$k$ money can exceed $N/k$ by one bid per bidder, which the paper absorbs into its small-bid assumption.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 11, Lemma 7 and the opening lines of its proof

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

namespace AdWordsMSVV.Tradeoff
theorem lemma_7 {N M : ℕ} (k : ℕ) (hk : 1 ≤ k) (ψ : ℕ → ℝ)
    (hψ : AntitoneOn ψ (Set.Icc 1 k)) (hψ0 : ∀ i ∈ Set.Icc 1 k, 0 ≤ ψ i) (hψk : ψ k = 0)
    (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (hσ : IsRun ψ k bid σ)
    (τ : Fin M → Option (Fin N)) :
    let α : ℕ → ℝ := fun i =>
      ∑ t : Fin M, match τ t with
        | none => 0
        | some b => if typeOf k bid σ b = i then bid b t else 0
    let β : ℕ → ℝ := fun i =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin M => slabQ k bid σ t = i), algRev bid σ t
    ∑ i ∈ Finset.Icc 1 (k - 1), ψ i * (α i - β i) ≤ (N : ℝ) / k := by sorry
end AdWordsMSVV.Tradeoff
