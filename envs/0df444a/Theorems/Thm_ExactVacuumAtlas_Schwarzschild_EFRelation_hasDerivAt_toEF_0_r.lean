-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_EFRelation_hasDerivAt_toEF_0_r
-- name    : ExactVacuumAtlas.Schwarzschild.EFRelation.hasDerivAt_toEF_0_r
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:33:42.322433+00:00
-- url     : https://prove2.me/theorems/34b6408f-eb74-44e8-9e57-9edbec6f1051
-- title:
--   Radial derivative of the Eddington–Finkelstein time coordinate
-- statement:
--   Let $M,\varepsilon$ be real numbers and $x=(t,r,\theta,\varphi)\in U^{\rm std}_M=\{r>0,\ r\neq2M,\ 0<\theta<\pi\}$. The first component of the map $\Phi_{M,\varepsilon}(t,r,\theta,\varphi)=\big(t+\varepsilon(r+2M\log\lvert r-2M\rvert),\ r,\ \theta,\ \varphi\big)$, as a function of the radial coordinate alone, has at $u=r$ the derivative $$\frac{\partial}{\partial r}\Big(t+\varepsilon\big(r+2M\log\lvert r-2M\rvert\big)\Big)=\varepsilon\Big(1+\frac{2M}{r-2M}\Big).$$
--
--   The only nontrivial entry of the Jacobian of relations R1/R2 (ingoing $\varepsilon=1$, outgoing $\varepsilon=-1$); the other entries are constants.
--
--   **Formalization Note** Mathlib's real logarithm satisfies $\log x=\log|x|$, so the formula and the derivative are valid on both sides of $r=2M$; the point $r=2M$ itself is excluded by the domain.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Schwarzschild/EFRelation.lean#L81-L95 (module Atlas.Schwarzschild.EFRelation, file sha256 c34cc5912defa1555f6c1fdc81e737294b0daaf9458bcb4fed544daf7d174e70; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_EFRelation_hasDerivAt_toEF_0_r.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFCertParts
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.EFRelation
set_option maxHeartbeats 4000000
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.EFRelation.hasDerivAt_toEF_0_r {x : Pt 4} (hx : x ∈ domStd M) :
    HasDerivAt (fun u => toEF M ε (Function.update x 1 u) 0)
      (ε * (1 + 2 * M / (x 1 - 2 * M))) (x 1) := by sorry
