-- Prove2me | Theorems.Thm_DualSSD_Duality_Supplement_mean_tailGini_monotone
-- name    : DualSSD.Duality.Supplement.mean_tailGini_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:41:17.998628+00:00
-- url     : https://prove2.me/theorems/3d053293-2402-4dfa-a618-289bf65bee9e
-- title:
--   Proposition 4.6 — tail-Gini 1-consistency
-- statement:
--   Let $X,Y$ be integrable real random variables on the same probability space $(\Omega,\mathcal B,P)$. Write $\mu_X=E_P X$ and let
--   $$G_X(p)=\frac{2}{p^2}\int_0^p\bigl(\mu_X\alpha-F_X^{(-2)}(\alpha)\bigr)\,d\alpha$$
--   be the tail Gini measure, where $F_X^{(-2)}$ is the integrated left quantile. For every $0<p\le1$,
--   $$X\succeq_{\rm SSD}Y\quad\Longrightarrow\quad\mu_X-G_X(p)\ge\mu_Y-G_Y(p).$$
--   This is 1-consistency of the mean–tail-Gini model with weak second-degree stochastic dominance. It supplies the objective monotonicity used in the companion optimization result; it imposes no symmetry or bounded-support assumption.
--
--   **Formalization Note** SSD compares the integrated distribution functions from (2.2). The published tail-Gini definition retains the factor $2/p^2$. Both integrability binders express the source's standing domain; $p=1$ is included.
--
--   Differences from the source:
--   - reading: The proposition does not repeat E|X|<∞ → Integrable X P and Integrable Y P are explicit; reason: these are the standing integrability assumptions for the performance and quantile functions on p. 65; no distributions in the intended domain are excluded
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13(1):60–78 (2002), DOI 10.1137/S1052623400375075, p. 72 (PDF page 13), Proposition 4.6, eqs. (4.8)–(4.9)

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.Duality.Supplement

open MeasureTheory

/-- Proposition 4.6, p. 72: tail-Gini 1-consistency on all of L1, including p=1. -/
theorem mean_tailGini_monotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) (hXY : DualSSD.Shared.SSD P X Y) :
    DualSSD.MeanRisk.mean P Y - DualSSD.MeanRisk.tailGini P Y p ≤
      DualSSD.MeanRisk.mean P X - DualSSD.MeanRisk.tailGini P X p := by sorry

end DualSSD.Duality.Supplement
