-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_certificate_influence
-- name    : AaronsonAmbainis.Short.certificate_influence
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-12T07:38:59.234196+00:00
-- url     : https://prove2.me/theorems/3f280a88-7688-4b00-abec-65b0b6eb65dc
-- title:
--   Fractional certificates on both sides give an influential coordinate: $\max_i I_i(G)\ge\delta_0\delta_1/(\gamma_0\gamma_1)$
-- statement:
--   Let $G:\{0,1\}^n\to\{0,1\}$ and, for $b\in\{0,1\}$, let $U_b\subseteq G^{-1}(b)$ have density $\delta_b=|U_b|/2^n$. Suppose every $x\in U_b$ has a fractional certificate $c^x\in\mathbb R^n_{\ge0}$ (that is, $\sum_{i\in S}c^x_i\ge1$ whenever $G(x^S)\ne G(x)$) with $\lVert c^x\rVert_1\le\gamma_b$. If $I_i(G)=\Pr_X[G(X)\ne G(X^{i})]\le\tau$ for all $i$, then
--
--   $$\delta_0\,\delta_1\le\gamma_0\,\gamma_1\,\tau.$$
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Lemma 4.

import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.certificate_influence {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Cube ι → Bool) (c : Cube ι → ι → ℝ) (U0 U1 : Finset (Cube ι)) (γ0 γ1 : ℝ)
    (hγ0 : 0 < γ0) (hγ1 : 0 < γ1)
    (h0 : ∀ x ∈ U0, G x = false ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ0)
    (h1 : ∀ x ∈ U1, G x = true ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ1)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : ∀ j, infl G j ≤ τ) :
    ((U0.card : ℝ) / 2 ^ Fintype.card ι) * ((U1.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ γ0 * γ1 * τ := by sorry
