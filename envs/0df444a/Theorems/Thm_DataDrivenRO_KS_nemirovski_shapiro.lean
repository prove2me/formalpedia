-- Prove2me | Theorems.Thm_DataDrivenRO_KS_nemirovski_shapiro
-- name    : DataDrivenRO.KS.nemirovski_shapiro
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:44:37.599904+00:00
-- url     : https://prove2.me/theorems/d3de75af-9fb0-4d0a-b9b7-33ca3e5646e2
-- title:
--   p. 16 — Nemirovski–Shapiro bound VaR^ℙ_ε(v) ≤ λ log(1/ε) + λ Σᵢ log E^{ℙᵢ}[e^{vᵢũᵢ/λ}] for independent marginals
-- statement:
--   Let $\mathbb P_1,\dots,\mathbb P_d$ be Borel probability measures on $\mathbb R$, each carried by some compact interval, and let $\mathbb P=\prod_{i=1}^d\mathbb P_i$ be their product on $\mathbb R^d$ (so the coordinates $\tilde u_1,\dots,\tilde u_d$ are independent). Let $0<\epsilon<1$ and $v\in\mathbb R^d$. Then for every $\lambda>0$,
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(v)\le\lambda\log(1/\epsilon)+\lambda\sum_{i=1}^d\log\mathbb E^{\mathbb P_i}\big[e^{v_i\tilde u_i/\lambda}\big].$$
--   Equivalently, $\mathrm{VaR}^{\mathbb P}_\epsilon(v)$ is at most the infimum of the right-hand side over $\lambda>0$.
--
--   This is the bound the paper attributes to Nemirovski and Shapiro (2006) and uses as Step 2 of its schema: it reduces the Value at Risk of a sum of independent terms to one-dimensional exponential moments.
--
--   **Formalization Note** The page writes $\inf_{\lambda\ge0}$; the statement is given for every $\lambda>0$, where the expression is defined. The compact-support hypothesis is the standing assumption of §5.1 (the support lies in a known box); it makes every exponential moment finite, so the Lean integral is the true expectation and not the junk value $0$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §5.1, display before (16), p. 16 (citing Nemirovski & Shapiro 2006)

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem nemirovski_shapiro {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    VaR (Measure.pi Q) ε v ≤
      lam * Real.log (1 / ε) + lam * ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) := by sorry

end DataDrivenRO.KS
