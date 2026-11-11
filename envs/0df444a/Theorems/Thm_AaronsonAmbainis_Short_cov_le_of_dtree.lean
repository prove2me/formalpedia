-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_cov_le_of_dtree
-- name    : AaronsonAmbainis.Short.cov_le_of_dtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:25:14.833377+00:00
-- url     : https://prove2.me/theorems/3f0070cd-d094-419a-ad43-61fb69b8ad43
-- title:
--   Covariance with a depth-$D$ decision tree is at most $\tfrac D2\max_j\mathbb E|p(X)-p(X^{j})|$
-- statement:
--   Let $p,h:\{0,1\}^n\to\mathbb R$ with $|h|\le 1$, and suppose $h$ is computed by a deterministic decision tree making at most $D$ queries on every input. If $\mathbb E_X|p(X)-p(X^{j})|\le M$ for every coordinate $j$, where $X^{j}$ is $X$ with bit $j$ flipped, then
--
--   $$\big|\operatorname{Cov}(p,h)\big|=\big|\mathbb E[(p-\mathbb E p)\,h]\big|\le\frac D2\,M.$$
--
--   This is the O'Donnell-Saks-Schramm-Servedio inequality with the query probabilities bounded by the depth. Expectations are uniform over the cube; `DTree D h` is the decision-tree predicate and `meanAbsIncr p j` is $\mathbb E|p(X)-p(X^{j})|$.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Lemma 6; after O'Donnell, Saks, Schramm and Servedio, Every decision tree has an influential variable, FOCS 2005.

import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.cov_le_of_dtree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p h : Cube ι → ℝ) (D : ℕ) (hD : Short.DTree D h) (hb : ∀ x, |h x| ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr p j ≤ M) :
    |mean (fun x => (p x - mean p) * h x)| ≤ (D : ℝ) / 2 * M := by sorry
