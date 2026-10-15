-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Std_lorentz
-- name    : ExactVacuumAtlas.Schwarzschild.Std.lorentz
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:32:01.361717+00:00
-- url     : https://prove2.me/theorems/920e25dc-5fa1-4362-85be-e70a44398429
-- title:
--   Standard Schwarzschild metric is Lorentzian on its domain
-- statement:
--   Let $M$ be a real number and $x\in U^{\rm std}_M=\{r>0,\ r\neq2M,\ 0<\theta<\pi\}$. Then the matrix $g^{\rm std}_M(x)$ of the **standard Schwarzschild metric** $g^{\rm std}_M$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-(1-2M/r)$, $g_{rr}=1/(1-2M/r)$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{tt}=-1/(1-2M/r)$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$ is Lorentzian: there is a matrix $E$ with invertible determinant and $E^{\mathsf T}g^{\rm std}_M(x)E=\mathrm{diag}(-1,1,1,1)$.
--
--   Signature obligation of row 3, valid on both the exterior ($r>2M$) and, for $M>0$, the interior ($0<r<2M$) component, where $\partial_r$ is the timelike direction and the frame columns are swapped.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eq. schwarzschildSpherical (r_s = 2M, G = c = 1); Sylvester's law of inertia (standard linear algebra); Mathlib LinearAlgebra/QuadraticForm/Signature.lean (pinned 0df444a3) for sigPos/sigNeg; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Schwarzschild/StdCert.lean#L45-L62 (module Atlas.Schwarzschild.StdCert, file sha256 af33bb6c24af47532c603f4130fa033f22bfd853620a67c4f6b1b62c7014a1b4; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_Std_lorentz.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.Std
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.Std.lorentz (M : ℝ) (x : Pt 4) (hx : x ∈ domStd M) : IsLorentzian (metricMatrix (gStd M) x) := by sorry
