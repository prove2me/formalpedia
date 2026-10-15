-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_R3_contDiffOn_toIn
-- name    : ExactVacuumAtlas.Kerr.R3.contDiffOn_toIn
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:22:36.42998+00:00
-- url     : https://prove2.me/theorems/1341b0fe-c52e-47ba-af42-7df5f08517ea
-- title:
--   Boyer–Lindquist to ingoing Kerr map is smooth on the regular domain (generic antiderivatives)
-- statement:
--   Let $M,a$ be real numbers, $\Delta=r^2-2Mr+a^2$, and let $H_1,H_2:\mathbb R\to\mathbb R$ be $C^\infty$ on the set $\{r:\Delta(r)\neq0\}$. Define $$\Phi_{H_1,H_2}(t,r,\theta,\varphi)=\big(t+r+H_1(r),\ r,\ \theta,\ -\varphi-H_2(r)\big).$$ Then $\Phi_{H_1,H_2}$ is $C^\infty$ on the Boyer–Lindquist regular domain $U^{\rm BL}_{M,a}=\{x:\ \Sigma\neq0,\ \Delta\neq0,\ \sin\theta\neq0\}$ ($\Sigma=r^2+a^2\cos^2\theta$).
--
--   Generic smoothness obligation of relation R3, proved for arbitrary antiderivatives $H_1,H_2$ and instantiated with the explicit ones in `ExactVacuumAtlas.Release01.R3_boyerLindquist_ingoing`.
--
--   **Formalization Note** The smoothness hypotheses on $H_1,H_2$ are section variables included into the statement; $C^\infty$ is `ContDiffOn ℝ ∞`.
-- source:
--   M. Visser, arXiv:0706.0622, eqs. (E:BL-change-1), (E:BL-change-2), (E:BL-change-3): u = t + r, t = t_BL + 2M∫ r dr/Δ, φ = −φ_BL − a∫ dr/Δ; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/R3.lean#L102-L114 (module Atlas.Kerr.R3, file sha256 8c3daf73ffed5d59070e65502f367d8325cf71e38068784dd6b32e7621d72d5c; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_R3_contDiffOn_toIn.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Kerr_Domain
import Definitions.Def_Atlas_Kerr_InDefs
import Definitions.Def_Atlas_Kerr_R3
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Kerr
open ExactVacuumAtlas
open ExactVacuumAtlas.Kerr
open ExactVacuumAtlas.Kerr.R3
set_option maxHeartbeats 4000000
variable (M a : ℝ) (H₁ H₂ : ℝ → ℝ)
variable (h₁ : ContDiffOn ℝ ∞ H₁ (radDom M a)) (h₂ : ContDiffOn ℝ ∞ H₂ (radDom M a))
include h₁ h₂

theorem ExactVacuumAtlas.Kerr.R3.contDiffOn_toIn : ContDiffOn ℝ ∞ (toIn H₁ H₂) (domBL M a) := by sorry
