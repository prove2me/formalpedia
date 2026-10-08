-- Prove2me | Theorems.Thm_BootRobust_Perf_nw_C_convex_inf
-- name    : BootRobust.Perf.nw_C_convex_inf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:37.66099+00:00
-- url     : https://prove2.me/theorems/19438d4b-6672-4bb4-be2a-616b4da4bb94
-- title:
--   B.6, p. 30 — the Nadaraya–Watson set C = {D : E_D > c̄_n} is convex and inf_{D∈C} B(D, D_tr) ≥ r
-- statement:
--   Let $w>0$ be weights and $\ell$ losses on $\Omega_n$, let $D_{\mathrm{tr}}\in\mathcal D_n$ have all entries positive and $r\in\mathbb R$. Write $E_D=\sum_iw_i\ell_iD_i/\sum_iw_iD_i$ for the Nadaraya–Watson estimator and $\bar c_n=\sup\{E_D: D\in\mathcal D_n,\ B(D,D_{\mathrm{tr}})\le r\}$ for its robust budget. Then the set
--   $$\mathcal C=\{D\in\mathcal D_n:\ E_D>\bar c_n\}$$
--   is convex, and
--   $$\inf_{D\in\mathcal C}B(D,D_{\mathrm{tr}})\ge r .$$
--
--   These are the two facts behind Corollary 2: the disappointment event of the robust Nadaraya–Watson formulation is a convex set at bootstrap distance at least $r$ from the training distribution.
--
--   **Formalization Note** The page describes $\mathcal C$ by the linear inequality $\sum w\ell D>\bar c_n\sum wD$, equivalent to $E_D>\bar c_n$ since $\sum_iw_iD_i>0$ on $\mathcal D_n$; the ratio form is used so that $\bar c_n=\pm\infty$ needs no special case. The page prints "$>r$" for the infimum; $\ge r$ is stated.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.6 (proof of Corollary 2), p. 30

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Proof of Corollary 2 (B.6, p. 30): the set `C` of distributions whose Nadaraya–Watson
estimate exceeds the robust budget `c̄_n` is convex, and `inf_{D ∈ C} B(D, D_tr) ≥ r`. -/
theorem nw_C_convex_inf {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (ℓ : ι → ℝ) :
    Convex ℝ {D | D ∈ stdSimplex ℝ ι ∧ nwBudget w ℓ Dtr r < ((nwEst w ℓ D : ℝ) : EReal)} ∧
      (r : EReal) ≤ ⨅ D ∈ {D | D ∈ stdSimplex ℝ ι ∧
        nwBudget w ℓ Dtr r < ((nwEst w ℓ D : ℝ) : EReal)}, bootDist D Dtr := by sorry

end BootRobust.Perf
