-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_priority_supersedes_wc
-- name    : DaiWeissFluid.LuKumar.priority_supersedes_wc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:20:46.825921+00:00
-- url     : https://prove2.me/theorems/70ea76c3-c17e-41ff-8048-a231ff5864d2
-- title:
--   Equation (4.4) implies work conservation (1.13)
-- statement:
--   For a reentrant line with positive service times, every fluid solution satisfying the preemptive-resume priority condition (4.4) also satisfies the work-conserving condition (1.13):
--   $$\operatorname{PrioritySolution}_{\pi}(Q,T)\Longrightarrow\operatorname{WorkConserving}(Q,T).$$
--   This connects the Lu–Kumar priority policy to the class of all work-conserving fluid models.
--
--   **Formalization Note** The implication uses the interval forms of the two complementarity conditions. It includes stations with empty constituencies; their work-conserving condition is vacuous. Classes and stations are zero-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 123, paragraph following Proposition 4.1: “condition (4.4) supersedes condition (1.13)”

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- On p. 123, (4.4) supersedes the work-conserving condition (1.13). -/
theorem priority_supersedes_wc {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (π : Equiv.Perm (Fin K))
    (Q T : ℝ → Fin K → ℝ) :
    L.IsPrioritySolution π Q T → L.IsWorkConserving Q T := by sorry

end DaiWeissFluid.LuKumar
