-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_theorem_7
-- name    : AssortSearch.HeurEq.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:02.211804+00:00
-- url     : https://prove2.me/theorems/b2c6b30e-d5c4-445b-a7f8-16513d31c27e
-- title:
--   Theorem 7: the no-search model under-estimates no-purchase demand for narrower and over-estimates it for deeper assortments
-- statement:
--   Consider the independent assortment search model with variants labelled by decreasing preference, $v_1\ge\dots\ge v_n>0$, $v_0>0$ and $\lambda>0$. Take any assortment $1\le x\le n$ and the preferences estimated from it, $\hat v(x)=(\hat v_0(x),\dots,\hat v_x(x),\hat v_{x+1}(n),\dots,\hat v_n(n))$. Then:
--
--   1. for any narrower assortment $x'<x$, the no-search model under-estimates the no-purchase demand,
--   $$d_0(x')\ \ge\ q_0^m(x'\mid\hat v(x));$$
--   2. for any deeper assortment $x<x''\le n$, it over-estimates the no-purchase demand,
--   $$d_0(x'')\ \le\ q_0^m(x''\mid\hat v(x)).$$
--
--   Here $d_0$ is the true no-purchase demand of the independent assortment model and $q_0^m(\cdot\mid\hat v(x))=\hat v_0(x)/(\hat v_0(x)+\sum_{j\le\cdot}\hat v_j(x))$ is the no-search model's prediction with the estimated preferences. Because consumer search is more likely in narrower assortments but is not reflected in the estimates, a retailer using the no-search model over-estimates its demand with narrower assortments and under-estimates it with deeper ones.
--
--   **Formalization Note** Independent assortment model only (the paper dismisses the overlapping case with "the similar logic"). $x'=0$ is allowed, where $d_0(0)=1$. The labelling $v_1\ge\dots\ge v_n$ (`Antitone v`) is the paper's standing convention of §3 and §5.1. $\lambda>0$ is a free parameter.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 22 (PDF 24), Theorem 7

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Theorem 7 (p. 22), independent assortment model. Take any assortment `1 ≤ x ≤ n` and the
preferences `v̂(x)` estimated from it. With any narrower assortment `x' < x` the no-search model
under-estimates the no-purchase demand, `d_0(x') ≥ q_0^m(x' | v̂(x))`; with any deeper assortment
`x < x'' ≤ n` it over-estimates it, `d_0(x'') ≤ q_0^m(x'' | v̂(x))`. -/
theorem theorem_7 {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    (∀ x' : ℕ, x' < x →
        shareNoPurchase (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x' ≤
          demandNoPurchase lam v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        demandNoPurchase lam v v0 x'' ≤
          shareNoPurchase (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x'') := by sorry

end AssortSearch.HeurEq
