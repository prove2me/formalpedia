-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_lorentz
-- name    : ExactVacuumAtlas.Kerr.lorentz
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:24:16.153198+00:00
-- url     : https://prove2.me/theorems/6a0b26cf-bcaa-4aac-8d3f-734589dd4a29
-- title:
--   Boyer–Lindquist Kerr metric is Lorentzian on the whole regular domain
-- statement:
--   Let $M,a$ be real numbers, $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$, and $x\in U^{\rm BL}_{M,a}=\{\Sigma\neq0,\Delta\neq0,\sin\theta\neq0\}$. Then the matrix $g^{\rm BL}(x)$ of the **Boyer–Lindquist Kerr metric** (platform definition `KerrBL_Kerr_Metric`, coordinates $(t,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$): $g_{tt}=-\big(1-\tfrac{2Mr}{\Sigma}\big)$, $g_{rr}=\tfrac{\Sigma}{\Delta}$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=\big(r^2+a^2+\tfrac{2Ma^2r\sin^2\theta}{\Sigma}\big)\sin^2\theta$, $g_{t\varphi}=g_{\varphi t}=-\tfrac{2Mar\sin^2\theta}{\Sigma}$, other entries $0$, with its closed-form candidate inverse $\hat g$ ($\hat g^{rr}=\Delta/\Sigma$, $\hat g^{\theta\theta}=1/\Sigma$ and a $(t,\varphi)$ block with denominator $\Sigma\Delta\sin^2\theta$) is Lorentzian: there is a matrix $E$ with invertible determinant and $E^{\mathsf T}g^{\rm BL}(x)E=\mathrm{diag}(-1,1,1,1)$.
--
--   Signature obligation of row 6. The proof exhibits the unnormalised Carter-type frame $T_0=(r^2+a^2)\partial_t+a\partial_\varphi$, $T_1=\partial_r$, $T_2=\partial_\theta$, $T_3=a\sin^2\theta\,\partial_t+\partial_\varphi$ with $T^{\mathsf T}gT=\mathrm{diag}(-\Delta\Sigma,\Sigma/\Delta,\Sigma,\Sigma\sin^2\theta)$ for $\Delta>0$, and the same columns with $T_0,T_1$ swapped for $\Delta<0$; no part of the regular domain ($\Delta<0$, $r<0$, $g_{tt}\ge0$) is excluded.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); Sylvester's law of inertia (standard linear algebra); Mathlib LinearAlgebra/QuadraticForm/Signature.lean (pinned 0df444a3) for sigPos/sigNeg; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/Frame.lean#L81-L111 (module Atlas.Kerr.Frame, file sha256 5a92b81fee538de9260bd7366efb75564a03d8023a764de125f0f9562b79d07a; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_lorentz.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Kerr_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real

theorem ExactVacuumAtlas.Kerr.lorentz (M a : ℝ) (x : Pt 4) (hx : x ∈ domBL M a) :
    IsLorentzian (metricMatrix (KerrBL.gKerr M a) x) := by sorry
