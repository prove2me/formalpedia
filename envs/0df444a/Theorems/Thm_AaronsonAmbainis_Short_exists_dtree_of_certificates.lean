-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_exists_dtree_of_certificates
-- name    : AaronsonAmbainis.Short.exists_dtree_of_certificates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-12T07:39:39.240841+00:00
-- url     : https://prove2.me/theorems/54203bfb-a3be-4371-8ca9-318acac4630d
-- title:
--   Fractional certificates of weight $\gamma$ on $U$ give a depth-$s$ decision tree with error $e$ on $U$, $s\,e^2\le\gamma^2I(G)$
-- statement:
--   Let $G:\{0,1\}^n\to\{0,1\}$, $U\subseteq\{0,1\}^n$ and $\gamma>0$, and suppose every $x\in U$ has a fractional certificate $\lambda^x$ of $G$ with $\lVert\lambda^x\rVert_1\le\gamma$. Then for every $s$ there is $F$ computed by a decision tree of depth at most $s$ with
--
--   $$s\cdot\Big(\frac{|\{x\in U:F(x)\ne G(x)\}|}{2^n}\Big)^2\le\gamma^2\,I(G).$$
--
--   Certificates are needed only on $U$; the influential coordinate on each subcube comes from the certificate-influence lemma.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Theorem 2.

import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.exists_dtree_of_certificates {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (U : Finset (Cube ι)) (γ : ℝ) (hγ : 0 < γ)
    (hU : ∀ x ∈ U, IsRow G x (lam x) ∧ ∑ j, lam x j ≤ γ) (s : ℕ) :
    ∃ F : Cube ι → Bool, Short.DTree s F ∧
      (s : ℝ) * (((U.filter fun x => F x ≠ G x).card : ℝ) / 2 ^ Fintype.card ι) ^ 2
        ≤ γ ^ 2 * ∑ j, infl G j := by sorry
