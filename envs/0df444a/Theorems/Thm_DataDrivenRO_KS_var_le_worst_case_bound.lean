-- Prove2me | Theorems.Thm_DataDrivenRO_KS_var_le_worst_case_bound
-- name    : DataDrivenRO.KS.var_le_worst_case_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:03.020063+00:00
-- url     : https://prove2.me/theorems/2d821bb3-c77f-44da-9495-90a13766bd96
-- title:
--   (16) with Theorem EC.2, p. 16 / p. ec4 — VaR^ℙ_ε(v) over 𝒫^I is at most the expression of (19) at every λ > 0
-- statement:
--   In the setting of §5.1 (with $N\ge1$, $0<\Gamma<1$, ordered $\hat u^{(0)}_i\le\dots\le\hat u^{(N+1)}_i$ and $0<\epsilon<1$), let $\mathbb P\in\mathcal P^I$, i.e. $\mathbb P=\prod_i\mathbb P_i$ with $\mathbb P_i\in\mathcal P^{KS}_i$. Then for every $v\in\mathbb R^d$ and every $\lambda>0$,
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(v)\le\lambda\log(1/\epsilon)+\lambda\sum_{i=1}^d\log\Big[\max\Big(\sum_{j=0}^{N+1}q^L_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda},\ \sum_{j=0}^{N+1}q^R_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda}\Big)\Big].$$
--
--   This is display (16) — the worst case over $\mathcal P^I$ of the Nemirovski–Shapiro bound — with the inner supremum evaluated by Theorem EC.2 for the monotone function $u\mapsto e^{v_iu/\lambda}$. Its right-hand side is exactly the expression whose infimum over $\lambda$ is (19).
--
--   **Formalization Note** The bound is stated for each $\lambda>0$ (equivalently, for the infimum over $\lambda>0$); the page's $\lambda\ge0$ has the same infimum.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (16), p. 16; EC.1.4, proof of Theorem 5, first sentence, p. ec4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem var_le_worst_case_bound {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ productRegion uhat Γ) (v : Fin d → ℝ)
    (lam : ℝ) (hlam : 0 < lam) :
    VaR P ε v ≤ boundKS uhat Γ ε v lam := by sorry

end DataDrivenRO.KS
