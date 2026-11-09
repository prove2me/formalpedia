-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_3_3
-- name    : DetPermanentApprox.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:42.537225+00:00
-- url     : https://prove2.me/theorems/a9897ed0-b49c-4863-9dbb-7dc575460bb8
-- title:
--   Lemma 3.3 — Value, Hessian and gradient approximation errors
-- statement:
--   Let $G$ be any finite simple graph on $N\ge2$ vertices, let rational $K\ge1$, and let $m\ge0$ and $y\in D_K$. Put $E_m(e^y)=\log Z_G(e^y)-T_m(e^y)$ and $W(e^y)=\sum_e e^{y_e}$. Then
--
--   $$|E_m(e^y)|\le\beta_m W(e^y),\qquad |a^\top\nabla_y^2 E_m(e^y)a|\le\beta_m\sum_e e^{y_e}a_e^2\quad(a\in\mathbb R^E),$$
--
--   and, for every edge $e$, $|\partial_e E_m(e^y)|\le\beta_m e^{y_e}$. All three bounds include $m=0$. This supplies the value, curvature and gradient errors needed by the surrogate and numerical procedure.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: the Hessian quadratic form → the second ambient Frechet derivative in the repeated direction a; reason: the smooth real error function has this exact Hessian quadratic form; the derivative is not restricted to D_K
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 3.3, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_3_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : IsSimple G) (hN : 2 ≤ Fintype.card V)
    (K : ℚ) (hK : 1 ≤ K) (m : ℕ) (y : E → ℝ) (hy : y ∈ degreeRegion G (K : ℝ)) :
    |errorFunction G K m y| ≤ (beta K m : ℝ) * weightSum (expWeights y) ∧
    (∀ a : E → ℝ,
      |fderiv ℝ (fun z => fderiv ℝ (errorFunction G K m) z a) y a| ≤
        (beta K m : ℝ) * ∑ e, Real.exp (y e) * a e ^ 2) ∧
    (∀ e, |partialR (errorFunction G K m) y e| ≤ (beta K m : ℝ) * Real.exp (y e)) := by sorry

end DetPermanentApprox.Main
