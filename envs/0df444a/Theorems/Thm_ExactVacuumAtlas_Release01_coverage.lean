-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release01_coverage
-- name    : ExactVacuumAtlas.Release01.coverage
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:49:46.116449+00:00
-- url     : https://prove2.me/theorems/60375f0c-ba23-42cc-a0b5-f42d3e3e077f
-- title:
--   Domain-coverage witnesses: $r=2M$ in EF, $\Delta<0$ in Boyer–Lindquist, $\Delta=0$ in ingoing Kerr
-- statement:
--   Three existence statements, with $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$ and the coordinate Ricci tensor $R_{bd}$ as in bundle `Atlas_Core_Basic`:
--
--   1. For every real $M>0$ there is a point $x\in U^{\rm EF}=\{r>0,\ 0<\theta<\pi\}$ with $r=2M$ at which all sixteen components $R_{bd}(x)$ of the ingoing Eddington–Finkelstein metric $g^{\rm EF}_{M,1}$ (with its candidate inverse) vanish.
--
--   2. For all real $M,a$ with $a^2<M^2$ there is a point $x\in U^{\rm BL}_{M,a}=\{\Sigma\neq0,\Delta\neq0,\sin\theta\neq0\}$ with $\Delta(r)<0$ at which all $R_{bd}(x)$ of the Boyer–Lindquist Kerr metric vanish.
--
--   3. For all real $M>0$ and $a$ with $a^2\le M^2$ there is a point $x\in U^{\rm in}_a=\{\Sigma\neq0,\sin\theta\neq0\}$ with $r^2-2Mr+a^2=0$ at which all $R_{bd}(x)$ of the ingoing Kerr metric vanish.
--
--   $$\forall M>0\ \exists x\in U^{\rm EF}:\ r=2M\wedge R^{\rm EF}_{bd}(x)=0;\quad \forall a^2<M^2\ \exists x\in U^{\rm BL}_{M,a}:\ \Delta<0\wedge R^{\rm BL}_{bd}(x)=0;\quad \forall M>0,\ a^2\le M^2\ \exists x\in U^{\rm in}_a:\ \Delta=0\wedge R^{\rm in}_{bd}(x)=0.$$
--
--   Documents that the certified domains are not narrowed to an exterior region: for $M>0$ the Eddington–Finkelstein certificate applies at points with $r=2M$ and $0<\theta<\pi$ (the regular-coordinate portion of $r=2M$; the polar axis, angular identifications and global horizon geometry are not included); for $a^2<M^2$ the Boyer–Lindquist certificate applies at points with $\Delta<0$, i.e. strictly between the two real roots of $\Delta$; for $M>0$, $a^2\le M^2$ the ingoing Kerr certificate applies at points with $\Delta=0$. These are the sufficient parameter regimes asserted by the three existence clauses; no necessary-and-sufficient parameter classification is claimed. The clauses exhibit regular coordinate points, not global horizons, and nothing causal or global is asserted about these loci.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Release01.lean#L176-L190 (module Atlas.Release01, file sha256 35a31e5ed932c61f239b2a15b3a2a9d8b3ba78368b5b471af95b0ec0e8e73c30; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Release01_coverage.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Kerr_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
import Definitions.Def_Atlas_Kerr_InParts
import Definitions.Def_Atlas_Kerr_R3
import Definitions.Def_Atlas_Minkowski_Cartesian
import Definitions.Def_Atlas_Minkowski_R4
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFCertParts
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open scoped ContDiff

theorem ExactVacuumAtlas.Release01.coverage :
    (∀ M : ℝ, 0 < M → ∃ x ∈ Schwarzschild.domEF, x 1 = 2 * M ∧
      ∀ b d, ricciOf (Schwarzschild.gEF M 1) (Schwarzschild.giEF M 1) b d x = 0) ∧
    (∀ M a : ℝ, a ^ 2 < M ^ 2 → ∃ x ∈ Kerr.domBL M a, KerrBL.Del M a (x 1) < 0 ∧
      ∀ b d, ricciOf (KerrBL.gKerr M a) (KerrBL.giKerr M a) b d x = 0) ∧
    (∀ M a : ℝ, 0 < M → a ^ 2 ≤ M ^ 2 → ∃ x ∈ Kerr.In.domIn a,
      x 1 ^ 2 - 2 * M * x 1 + a ^ 2 = 0 ∧
      ∀ b d, ricciOf (Kerr.In.gIn M a) (Kerr.In.giIn M a) b d x = 0) := by sorry
