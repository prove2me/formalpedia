-- Prove2me | Theorems.Thm_FRBSplitting_Linesearch_lemma_3_2
-- name    : FRBSplitting.Linesearch.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:27.333394+00:00
-- url     : https://prove2.me/theorems/3cee8bce-db3a-498d-9052-d891f1226a51
-- title:
--   Lemma 3.2, p. 10 — for locally Lipschitz B the linesearch (29)–(30) terminates
-- statement:
--   Let $H$ be a real Hilbert space, $A:H\rightrightarrows H$ maximally monotone with resolvents $J_{tA}$, and $B:H\to H$ locally Lipschitz. Let $\delta,\sigma\in(0,1)$, let $x_k,x_{k-1}\in H$ be arbitrary, let $\lambda_{k-1}>0$ and $\rho\in\{1,\sigma^{-1}\}$. Writing $x_{k+1}(t)=J_{tA}\big(x_k-tB(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)$ for the trial point at step $t$, there is a nonnegative integer $i$ such that the step $t=\rho\lambda_{k-1}\sigma^i$ satisfies the linesearch test (30):
--   $$\rho\lambda_{k-1}\sigma^i\,\big\|B(x_{k+1}(\rho\lambda_{k-1}\sigma^i))-B(x_k)\big\|\le\frac{\delta}{2}\,\big\|x_{k+1}(\rho\lambda_{k-1}\sigma^i)-x_k\big\|.$$
--
--   Hence the linesearch procedure of Algorithm 1 always terminates (the smallest such $i$ exists), so the step sizes $(\lambda_k)$ are well defined.
--
--   **Formalization Note.** "Always terminates" is stated as the existence of an index satisfying (30) at an arbitrary iteration state; the least such index then exists. No monotonicity of $B$ and no zero of $A+B$ is assumed, as on the page. $J$ is a resolvent family of $A$ (`hJ`).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 10, Lemma 3.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linesearch

theorem lemma_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBloc : LocallyLipschitz B)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (xk xkm1 : H) (lamPrev ρ : ℝ) (hlp : 0 < lamPrev) (hρ : ρ = 1 ∨ ρ = σ⁻¹) :
    ∃ i : ℕ, ρ * lamPrev * σ ^ i * ‖B (trialPoint J B lamPrev (ρ * lamPrev * σ ^ i) xk xkm1) - B xk‖ ≤
      δ / 2 * ‖trialPoint J B lamPrev (ρ * lamPrev * σ ^ i) xk xkm1 - xk‖ := by sorry

end FRBSplitting.Linesearch
