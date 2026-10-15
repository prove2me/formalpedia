-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_In_hasDerivAt_Ui_t
-- name    : ExactVacuumAtlas.Kerr.In.hasDerivAt_Ui_t
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:08:06.81569+00:00
-- url     : https://prove2.me/theorems/7f351042-b3cb-4207-b581-587993eb83b9
-- title:
--   Polar-angle derivative of $1/\Sigma$ for Kerr
-- statement:
--   Let $a,r,\theta$ be real numbers with $r^2+a^2\cos^2\theta\neq0$ and $U(r,\theta)=1/\Sigma=\big(r^2+a^2\cos^2\theta\big)^{-1}$. Then $t\mapsto U(r,t)$ has at $t=\theta$ the derivative $$\partial_\theta\Big(\frac1\Sigma\Big)=\frac{2a^2\sin\theta\cos\theta}{\Sigma^2}=2a^2\sin\theta\cos\theta\,U(r,\theta)^2.$$
--
--   Companion of the radial rule; together they are the two key derivative rules for the atom $1/\Sigma$. The generated ingoing-Kerr tables also use the usual product and chain rules, trigonometric derivatives, the derivative of $1/\sin\theta$, and locality arguments.
--
--   **Formalization Note** Stated with Mathlib's `HasDerivAt`; $\Sigma\neq0$ is the only hypothesis.
-- source:
--   elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/InAtoms.lean#L37-L48 (module Atlas.Kerr.InAtoms, file sha256 30e14f9094cc6659a7670a18a03040eb71977f1710ab1a059d8f086edad7527a; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_In_hasDerivAt_Ui_t.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
open Real

theorem ExactVacuumAtlas.Kerr.In.hasDerivAt_Ui_t (a r θ : ℝ) (h : r ^ 2 + a ^ 2 * cos θ ^ 2 ≠ 0) :
    HasDerivAt (fun t => Ui a r t) (2 * a ^ 2 * sin θ * cos θ * Ui a r θ ^ 2) θ := by sorry
