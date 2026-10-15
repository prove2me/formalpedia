-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_In_hasDerivAt_Ui_r
-- name    : ExactVacuumAtlas.Kerr.In.hasDerivAt_Ui_r
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:08:16.365261+00:00
-- url     : https://prove2.me/theorems/23a1bdbd-94f5-4b74-ba13-1d2448755821
-- title:
--   Radial derivative of $1/\Sigma$ for Kerr
-- statement:
--   Let $a,\theta,r$ be real numbers with $r^2+a^2\cos^2\theta\neq0$ and write $U(r,\theta)=\big(r^2+a^2\cos^2\theta\big)^{-1}=1/\Sigma$ (the atom `Ui` of bundle `Atlas_Kerr_InAtoms`). Then $u\mapsto U(u,\theta)$ has at $u=r$ the derivative $$\partial_r\Big(\frac1\Sigma\Big)=-\frac{2r}{\Sigma^2}=-2r\,U(r,\theta)^2.$$
--
--   One of the two key derivative rules for the atom $1/\Sigma$ used by the ingoing-Kerr tables, whose entries are polynomials in $r,\sin\theta,\cos\theta,1/\Sigma,1/\sin\theta$. Differentiating the tables also uses the usual product and chain rules, trigonometric derivatives, the derivative of $1/\sin\theta$, and locality arguments.
--
--   **Formalization Note** `Ui a r θ` is Mathlib's inverse of a real number; the hypothesis $\Sigma\neq0$ excludes the junk value of $0^{-1}=0$.
-- source:
--   elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/InAtoms.lean#L28-L35 (module Atlas.Kerr.InAtoms, file sha256 30e14f9094cc6659a7670a18a03040eb71977f1710ab1a059d8f086edad7527a; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_In_hasDerivAt_Ui_r.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
open Real

theorem ExactVacuumAtlas.Kerr.In.hasDerivAt_Ui_r (a θ r : ℝ) (h : r ^ 2 + a ^ 2 * cos θ ^ 2 ≠ 0) :
    HasDerivAt (fun u => Ui a u θ) (-2 * r * Ui a r θ ^ 2) r := by sorry
