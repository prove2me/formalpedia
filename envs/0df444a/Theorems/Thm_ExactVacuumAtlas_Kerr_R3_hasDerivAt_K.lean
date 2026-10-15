-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_R3_hasDerivAt_K
-- name    : ExactVacuumAtlas.Kerr.R3.hasDerivAt_K
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:21:37.08823+00:00
-- url     : https://prove2.me/theorems/d44aaf29-0eb9-4b59-a4de-438e8e3ae696
-- title:
--   The explicit antiderivative $K$ of $1/\Delta$ for Kerr, all parameter branches
-- statement:
--   Let $M,a$ be real numbers and $\Delta=r^2-2Mr+a^2$. Define $K_{M,a}:\mathbb R\to\mathbb R$ by cases on the sign of $M^2-a^2$: for $M^2>a^2$ with $b=\sqrt{M^2-a^2}$, $K(r)=\dfrac{\log\lvert r-(M+b)\rvert-\log\lvert r-(M-b)\rvert}{2b}$; for $M^2<a^2$ with $b=\sqrt{a^2-M^2}$, $K(r)=\dfrac{\arctan\big((r-M)/b\big)}{b}$; for $M^2=a^2$, $K(r)=-\dfrac1{r-M}$. Then for every $r$ with $\Delta(r)\neq0$, $$K'(r)=\frac1{\Delta(r)}.$$
--
--   Supplies the antiderivative of $1/\Delta$ used by the explicit R3 functions $H_1=M\log|\Delta|+2M^2K$ and $H_2=aK$, so that $H_1'=2Mr/\Delta$ and $H_2'=a/\Delta$ hold for every real $M,a$ (two real roots, double root, no real root).
--
--   **Formalization Note** Mathlib's real logarithm satisfies $\log x=\log|x|$, so the logarithmic branch is valid on both sides of each root; the case split is on $0<M^2-a^2$, $M^2-a^2<0$, else.
-- source:
--   M. Visser, arXiv:0706.0622, eqs. (E:BL-change-1), (E:BL-change-2), (E:BL-change-3): u = t + r, t = t_BL + 2M∫ r dr/Δ, φ = −φ_BL − a∫ dr/Δ; elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/R3.lean#L296-L308 (module Atlas.Kerr.R3, file sha256 8c3daf73ffed5d59070e65502f367d8325cf71e38068784dd6b32e7621d72d5c; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_R3_hasDerivAt_K.lean)

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
variable (M a : ℝ)

theorem ExactVacuumAtlas.Kerr.R3.hasDerivAt_K {r : ℝ} (hr : r ∈ radDom M a) : HasDerivAt (K M a) (1 / Delta M a r) r := by sorry
