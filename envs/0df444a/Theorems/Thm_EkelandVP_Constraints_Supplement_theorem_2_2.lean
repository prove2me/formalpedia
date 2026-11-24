-- Prove2me | Theorems.Thm_EkelandVP_Constraints_Supplement_theorem_2_2
-- name    : EkelandVP.Constraints.Supplement.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:24:57.967097+00:00
-- url     : https://prove2.me/theorems/384c21e8-6f81-4d61-8be3-42cd28d3d02a
-- title:
--   Theorem 2.2 — a nearby approximate critical point with strict radius
-- statement:
--   Let $V$ be a real Banach space and $F:V\to\mathbb R\cup\{+\infty\}$ lower semicontinuous and Gâteaux-differentiable at every finite point, with continuous linear derivative $F'(x)\in V^*$. Suppose $-\infty<\inf F<+\infty$. For every $\varepsilon>0$, every $u$ with $F(u)\le\inf F+\varepsilon$, and every $\lambda>0$, there is a finite point $v$ such that
--   $$
--   F(v)\le F(u),\qquad \|v-u\|<\lambda,\qquad
--   \|F'(v)\|_*\le\frac{\varepsilon}{\lambda}.
--   $$
--   All three conclusions apply to the same point, including when the starting objective gap equals $\varepsilon$. No continuity of $F'$ or open effective domain is required. This is the nearby-point derivative form of the variational principle.
--
--   Differences from the source:
--   - encoding: the codomain is real with an allowed value +∞ and finite infimum → EReal is used, with bottom < infimum < top, and the chosen point is explicitly finite; reason: the infimum hypotheses already exclude −∞ at every point; the published Gâteaux definition differentiates only locally finite directional restrictions
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 327, Theorem 2.2 (PDF 4); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_General_IsGateauxDiff
set_option autoImplicit false

namespace EkelandVP.Constraints.Supplement

/-- All three conclusions of Theorem 2.2, including the strict radius at equality
in the starting objective gap. No continuity of the derivative is assumed. -/
theorem theorem_2_2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (F : V → EReal) (F' : V → V →L[ℝ] ℝ)
    (hlsc : LowerSemicontinuous F)
    (hgateaux : EkelandVP.General.IsGateauxDiff F F')
    (hbelow : ⊥ < iInf F) (hproper : iInf F < ⊤)
    (ε : ℝ) (hε : 0 < ε) (u : V)
    (hu : F u ≤ iInf F + (ε : EReal)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ v : V, F v ≠ ⊤ ∧ F v ≤ F u ∧ ‖v - u‖ < lam ∧ ‖F' v‖ ≤ ε / lam := by sorry

end EkelandVP.Constraints.Supplement
