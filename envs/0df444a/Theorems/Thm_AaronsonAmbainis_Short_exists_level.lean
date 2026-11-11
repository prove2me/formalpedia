-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_exists_level
-- name    : AaronsonAmbainis.Short.exists_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:32.068013+00:00
-- url     : https://prove2.me/theorems/8c347a8f-25c3-4e62-b3eb-3f0b1703bb8c
-- title:
--   Some threshold $t\in[a,b]$ has $(b-a)\,I(\mathbf 1[f>t])\le\sum_j\mathbb E|f(X)-f(X^{j})|$
-- statement:
--   Let $f:\{0,1\}^n\to\mathbb R$ and $a<b$. There is $t\in[a,b]$ such that the level set $G_t=\mathbf 1[f>t]$ has total influence
--
--   $$(b-a)\sum_j\Pr_X\big[G_t(X)\ne G_t(X^{j})\big]\le\sum_j\mathbb E_X\big|f(X)-f(X^{j})\big|.$$
--
--   Indeed the left side integrated over $t\in[a,b]$ is at most the right side, since $G_t(x)\ne G_t(x^{j})$ only for $t$ between $f(x)$ and $f(x^{j})$.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Lemma 3 (threshold averaging).

import Definitions.Def_AaronsonAmbainis_Level_Rows
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.exists_level {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Cube ι → ℝ) (a b : ℝ) (hab : a < b) :
    ∃ t, a ≤ t ∧ t ≤ b ∧
      (b - a) * ∑ j, infl (Level.lev f t) j ≤ ∑ j, meanAbsIncr f j := by sorry
