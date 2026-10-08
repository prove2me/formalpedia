-- Prove2me | Theorems.Thm_FixpNash_DivFree_threshold_eq_sup_prefix
-- name    : FixpNash.DivFree.threshold_eq_sup_prefix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:42.303871+00:00
-- url     : https://prove2.me/theorems/ae47cabe-6496-4214-abfb-e24bef9d93c9
-- title:
--   Proof of Lemma 21, p. 48 — t_i = max_l ((Σ_{j≤l} z_ij) − 1)/l for the sorted vector z_i
-- statement:
--   Fix a finite game, a real vector $x$, and a player $i$ with $n_i\ge 1$ pure strategies. Let $y_i=(h_{ij}(x))_{j\in S_i}$ and let $z_i=(z_{i1},\dots,z_{in_i})$ be $y_i$ sorted in decreasing order, $z_{i1}\ge z_{i2}\ge\dots\ge z_{in_i}$. Then the threshold $t_i$ (the unique solution of $f_{i,x}(t)=1$) is
--   $$t_i=\max\Bigl\{\tfrac1l\Bigl(\sum_{j=1}^{l}z_{ij}-1\Bigr)\ :\ l=1,\dots,n_i\Bigr\}.$$
--
--   This closed form is what lets $G_I$ be computed by a circuit with gates $+,-,*,\max,\min$ and rational constants only (Lemma 21): a sorting network produces $z_i$, and the divisions are by the integer constants $l$.
--
--   **Formalization Note.** The sorted order is given by a bijection $e:\{0,\dots,n\}\to S_i$ (so $n_i=n+1$) along which $h_{i,e(l)}(x)$ is nonincreasing; the 0-based index $l$ corresponds to the paper's $l+1$, hence the denominator $l+1$ and the prefix $\{0,\dots,l\}$. The statement holds for every real vector $x$.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, proof of Lemma 21, p. 48

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- Proof of Lemma 21, p. 48: if `e` lists the `n + 1` strategies of player `i` so that
`zₗ = hᵢ,e(l)(x)` is decreasing in `l`, then
`tᵢ = max_{l = 1, …, n+1} ((∑_{k ≤ l} z_k) − 1) / l` (indices shifted to `Fin (n + 1)`).
Holds for every real vector `x`. -/
theorem threshold_eq_sup_prefix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) (i : ι) (n : ℕ) (e : Fin (n + 1) ≃ S i)
    (hz : Antitone (fun l : Fin (n + 1) => hVal u x i (e l))) :
    threshold u x i =
      Finset.univ.sup' Finset.univ_nonempty (fun l : Fin (n + 1) =>
        ((∑ k ∈ Finset.Iic l, hVal u x i (e k)) - 1) / ((l : ℕ) + 1 : ℝ)) := by sorry

end FixpNash.DivFree
