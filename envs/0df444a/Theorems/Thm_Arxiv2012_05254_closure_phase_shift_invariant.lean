-- Prove2me | Theorems.Thm_Arxiv2012_05254_closure_phase_shift_invariant
-- name    : Arxiv2012_05254.closure_phase_shift_invariant
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:42:40.073902+00:00
-- url     : https://prove2.me/theorems/7d131cb5-362d-43d4-a1a0-a6d9e85384ea
-- title:
--   Eq. (16): the closure phase does not depend on the phase centre
-- statement:
--   Let $x_0,x_1,x_2\in\mathbb R^2$ be the positions (in wavelengths) of a closed triad of array elements, with spacings $u_{a\lceil a+1\rfloor_3}=x_{\lceil a+1\rfloor_3}-x_a$. Let $\psi_{a\lceil a+1\rfloor_3}$ ($a=0,1,2$) be the phase offsets of three NPCs $2\pi u_{a\lceil a+1\rfloor_3}\cdot\hat s+\psi_{a\lceil a+1\rfloor_3}=0$. Move the phase centre to an arbitrary point $\hat s_0$, and let $\psi'_{a\lceil a+1\rfloor_3}=\psi_{a\lceil a+1\rfloor_3}+2\pi u_{a\lceil a+1\rfloor_3}\cdot\hat s_0$. Then:
--
--   1. Each NPC with phase $\psi'$ is the original NPC written in the shifted coordinates $\hat s'=\hat s-\hat s_0$ (eq. 15).
--   2. The closure phase is unchanged (eq. 16):
--
--   $$\psi_3'=\sum_{a=0}^2\psi'_{a\lceil a+1\rfloor_3}=\sum_{a=0}^2\psi_{a\lceil a+1\rfloor_3}+2\pi\,\hat s_0\cdot\sum_{a=0}^2u_{a\lceil a+1\rfloor_3}=\psi_3.$$
--
--   This is the image-plane form of the translation invariance of the closure phase.
--
--   **Formalization Note** The spacings are defined from the element positions, so the closed-loop condition (9) holds automatically.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c001; Section 3, eqs. (14)-(16), PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem closure_phase_shift_invariant (x : Fin 3 → Plane) (ψ : Fin 3 → ℝ) (s₀ : Plane) :
    (∀ a, npc (spacing x a) (recentredPhase (spacing x a) (ψ a) s₀) =
      (fun s => s - s₀) '' npc (spacing x a) (ψ a)) ∧
    closurePhase (fun a => recentredPhase (spacing x a) (ψ a) s₀) = closurePhase ψ := by sorry

end Arxiv2012_05254
