-- Prove2me | Theorems.Thm_Arxiv2012_05254_polygon_closure_phase_fan_sum
-- name    : Arxiv2012_05254.polygon_closure_phase_fan_sum
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:46:48.106321+00:00
-- url     : https://prove2.me/theorems/5ea3cb8f-643f-4a84-a9b3-f9e0f9665755
-- title:
--   Eq. (24): the closure phase of an $N$-polygon is the sum over its elemental triads
-- statement:
--   Let $N\ge3$ elements at positions $x_0,\dots,x_{N-1}$ form a closed $N$-polygon. Let $\psi_{ab}$ be NPC phase offsets for all ordered pairs, with $\psi_{ba}=-\psi_{ab}$ (conjugate baselines). For $q=1,\dots,N-2$, let $\psi_{3(q)}$ be the closure phase of the elemental triad $(0,q,q+1)$. Then
--
--   $$\psi_N=\sum_{a=0}^{N-1}\psi_{a\lceil a+1\rfloor_N}=\sum_{q=1}^{N-2}\psi_{3(q)}.$$
--
--   No non-collinearity is needed for this equality. If $x_{N-1},x_0,x_1$ are not collinear, the NPCs of the two sides meeting at element $0$ intersect. With any intersection point $\hat s_0$ as phase centre, these two NPCs have phase offset $0$, and (eq. 24)
--
--   $$\psi_N=\sum_{a=0}^{N-1}\psi'_{a\lceil a+1\rfloor_N},\qquad \psi'_{ab}=\psi_{ab}+2\pi u_{ab}\cdot\hat s_0.$$
--
--   **Formalization Note** The paper names the second fringe through $\hat s_0$ "$F_{N1}$". The fringe of the other side at element $0$, $F_{N-1,0}$, is used here; see the mission report. The triads are indexed from $0$ in Lean.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c022; Appendix 2, eqs. (23)-(24) and Fig. 10, PDF p. 16

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem polygon_closure_phase_fan_sum {M : ℕ} (hM : 1 ≤ M) (x : Fin (M + 2) → Plane)
    (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b) :
    closurePhase (loopPhase ψ id) = ∑ q : Fin M, closurePhase (loopPhase ψ (fanTriad q)) ∧
    (AffineIndependent ℝ ![x (Fin.last (M + 1)), x 0, x 1] →
      (∃ s₀ : Plane, s₀ ∈ npc (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) ∩
          npc (spacing x 0) (ψ 0 1)) ∧
      ∀ s₀ ∈ npc (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) ∩ npc (spacing x 0) (ψ 0 1),
        recentredPhase (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) s₀ = 0 ∧
        recentredPhase (spacing x 0) (ψ 0 1) s₀ = 0 ∧
        ∑ a, recentredPhase (spacing x a) (loopPhase ψ id a) s₀ = closurePhase (loopPhase ψ id)) := by sorry

end Arxiv2012_05254
