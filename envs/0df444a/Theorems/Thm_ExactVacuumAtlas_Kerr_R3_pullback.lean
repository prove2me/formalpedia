-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_R3_pullback
-- name    : ExactVacuumAtlas.Kerr.R3.pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:23:13.338179+00:00
-- url     : https://prove2.me/theorems/ed57f5c9-31b8-4218-9433-47586ccd3fc9
-- title:
--   Boyer–Lindquist to ingoing Kerr: pull-back identity of the metrics
-- statement:
--   Let $M,a$ be real numbers, $H_1,H_2:\mathbb R\to\mathbb R$ arbitrary, $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$, and $x=(t,r,\theta,\varphi)$ in the regular domain $U^{\rm BL}_{M,a}=\{x:\ \Sigma\neq0,\ \Delta\neq0,\ \sin\theta\neq0\}$. Let $\Phi=\Phi_{H_1,H_2}$ be the map $(t,r,\theta,\varphi)\mapsto(t+r+H_1(r),r,\theta,-\varphi-H_2(r))$ and let $$J(x)=\begin{pmatrix}1&\frac{r^2+a^2}{\Delta}&0&0\\0&1&0&0\\0&0&1&0\\0&-\frac a\Delta&0&-1\end{pmatrix}.$$ Then, with $g^{\rm BL}$ the **Boyer–Lindquist Kerr metric** (platform definition `KerrBL_Kerr_Metric`, coordinates $(t,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$): $g_{tt}=-\big(1-\tfrac{2Mr}{\Sigma}\big)$, $g_{rr}=\tfrac{\Sigma}{\Delta}$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=\big(r^2+a^2+\tfrac{2Ma^2r\sin^2\theta}{\Sigma}\big)\sin^2\theta$, $g_{t\varphi}=g_{\varphi t}=-\tfrac{2Mar\sin^2\theta}{\Sigma}$, other entries $0$, with its closed-form candidate inverse $\hat g$ ($\hat g^{rr}=\Delta/\Sigma$, $\hat g^{\theta\theta}=1/\Sigma$ and a $(t,\varphi)$ block with denominator $\Sigma\Delta\sin^2\theta$) and $g^{\rm in}$ the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed): $$J(x)^{\mathsf T}\,g^{\rm in}\big(\Phi(x)\big)\,J(x)=g^{\rm BL}(x).$$
--
--   The algebraic half of relation R3. Because $g^{\rm in}$ depends only on $(r,\theta)$, which $\Phi$ preserves, this identity does not involve $H_1,H_2$; it certifies the change of coordinates only together with the Jacobian theorem stating that $J$ consists of the genuine partial derivatives of $\Phi$ (which is where $H_1'=2Mr/\Delta$, $H_2'=a/\Delta$ enter). Both are combined in `ExactVacuumAtlas.Release01.R3_boyerLindquist_ingoing`.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   M. Visser, arXiv:0706.0622, eqs. (E:BL-change-1), (E:BL-change-2), (E:BL-change-3): u = t + r, t = t_BL + 2M∫ r dr/Δ, φ = −φ_BL − a∫ dr/Δ; R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/R3.lean#L193-L227 (module Atlas.Kerr.R3, file sha256 8c3daf73ffed5d59070e65502f367d8325cf71e38068784dd6b32e7621d72d5c; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_R3_pullback.lean)

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
omit h₁ h₂
variable (d₁ : ∀ r ∈ radDom M a, HasDerivAt H₁ (2 * M * r / Delta M a r) r)
variable (d₂ : ∀ r ∈ radDom M a, HasDerivAt H₂ (a / Delta M a r) r)
include d₁
omit d₁
include d₂
omit d₂
include d₁ d₂
omit d₁ d₂

theorem ExactVacuumAtlas.Kerr.R3.pullback {x : Pt 4} (hx : x ∈ domBL M a) :
    (jac M a x).transpose * metricMatrix (In.gIn M a) (toIn H₁ H₂ x) * jac M a x =
      metricMatrix (KerrBL.gKerr M a) x := by sorry
