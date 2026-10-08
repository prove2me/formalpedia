-- Prove2me | Theorems.Thm_BSUMConv_SUM_eq_10_11
-- name    : BSUMConv.SUM.eq_10_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:29.939803+00:00
-- url     : https://prove2.me/theorems/00fbab3b-387f-4254-bd66-a9675336a0f2
-- title:
--   (10)–(11), p. 7 — f(x^{r+1}) ≤ u(x^{r+1}, x^r) ≤ u(x^r, x^r) = f(x^r), so the SUM objective values are non-increasing
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^m$, $f:\mathbb R^m\to\mathbb R$, and let $u:\mathbb R^m\times\mathbb R^m\to\mathbb R$ satisfy (A1) $u(y,y)=f(y)$ for $y\in\mathcal X$ and (A2) $u(x,y)\ge f(x)$ for $x,y\in\mathcal X$. Let $x^0,x^1,\dots$ be a run of the SUM algorithm: $x^0\in\mathcal X$ and $x^{r+1}\in\arg\min_{x\in\mathcal X}u(x,x^r)$ for every $r$. Then for every $r=0,1,2,\dots$
--   $$
--   f(x^{r+1})\le u(x^{r+1},x^r)\le u(x^r,x^r)=f(x^r),
--   $$
--   and consequently the objective values are non-increasing:
--   $$
--   f(x^0)\ge f(x^1)\ge f(x^2)\ge\cdots.
--   $$
--
--   This is the descent property of the SUM algorithm, the first step of the proof of Theorem 1 and of Corollary 1 (the iterates stay in the level set $\mathcal X^0$).
--
--   **Formalization Note** The page attributes step (i) to (A1) and the last equality to (A2) and writes $x^{t+1}$ for $x^{r+1}$; these are slips of the text, and the statement here uses (A2) and (A1) where they are actually needed. Closedness and convexity of $\mathcal X$ are not used by this step and are not hypotheses.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 7, proof of Theorem 1, (10) and (11)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_SUM_Setting

namespace BSUMConv.SUM

/-- (10)–(11), p. 7: along a SUM run, `f(x^{r+1}) ≤ u(x^{r+1}, x^r) ≤ u(x^r, x^r) = f(x^r)` for every
`r`, so `f(x⁰) ≥ f(x¹) ≥ f(x²) ≥ ⋯`. -/
theorem eq_10_11 {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hA1 : AssumptionA1 Xset f u) (hA2 : AssumptionA2 Xset f u)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (hx : IsSUMRun Xset u x) :
    (∀ r : ℕ, f (x (r + 1)) ≤ u (x (r + 1)) (x r) ∧ u (x (r + 1)) (x r) ≤ u (x r) (x r) ∧
      u (x r) (x r) = f (x r)) ∧
    Antitone (fun r => f (x r)) := by sorry

end BSUMConv.SUM
