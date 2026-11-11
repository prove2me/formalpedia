-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_exists_dtree
-- name    : AaronsonAmbainis.Short.exists_dtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:06.070383+00:00
-- url     : https://prove2.me/theorems/92f0c63a-63e4-40b3-abf0-4bf9cc1c278b
-- title:
--   Fractional certificates of weight $\gamma$ on $U$ give a depth-$s$ decision tree with error $e$ on $U$, $s\,e^2\le\tfrac{\gamma^2}{4}I(G)$
-- statement:
--   Let $G:\{0,1\}^n\to\{0,1\}$ and let $\lambda^x\in\mathbb R^n_{\ge 0}$ be a fractional certificate of $G$ at every point $x$: $\sum_{j\in S}\lambda^x_j\ge 1$ whenever $G(x^S)\ne G(x)$. Let $U\subseteq\{0,1\}^n$ and $\gamma>0$ with $\lVert\lambda^x\rVert_1\le\gamma$ for all $x\in U$. Then for every $s$ there is a function $F$ computed by a decision tree of depth at most $s$ with
--
--   $$s\cdot\Big(\frac{|\{x\in U: F(x)\ne G(x)\}|}{2^n}\Big)^2\le\frac{\gamma^2}{4}\,I(G),\qquad I(G)=\sum_j\Pr_X[G(X)\ne G(X^{j})].$$
--
--   The tree queries, on each subcube, a coordinate whose influence is large by the two-sided certificate inequality, and the total influence pays for the queries.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Theorem 2 (with Lemma 4 supplied by Theorem 5.4 of Turturean, A proof of the Aaronson-Ambainis conjecture, arXiv:2611.09773).

import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.exists_dtree {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (hrow : ∀ x, IsRow G x (lam x))
    (U : Finset (Cube ι)) (γ : ℝ) (hγ : 0 < γ) (hU : ∀ x ∈ U, ∑ j, lam x j ≤ γ) (s : ℕ) :
    ∃ F : Cube ι → Bool, Short.DTree s F ∧
      (s : ℝ) * (((U.filter fun x => F x ≠ G x).card : ℝ) / 2 ^ Fintype.card ι) ^ 2
        ≤ γ ^ 2 / 4 * ∑ j, infl G j := by sorry
