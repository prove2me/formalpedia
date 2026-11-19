-- Prove2me | Theorems.Thm_AJOnline_KTaxi2_converse_bridge
-- name    : AJOnline.KTaxi2.converse_bridge
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:38:15.121217+00:00
-- url     : https://prove2.me/theorems/4b71d86c-dfb5-4a6f-ad78-3e59a98a5c8f
-- title:
--   Converse bridge: history-free lazy strategies come from memoryless policies
-- statement:
--   Fix $x_0$, and let $\beta$ be a behaviour strategy on the 2-taxi game satisfying three conditions at legal positions:
--
--   1. $\beta$ depends only on the current configuration and the last move;
--   2. after a request, $\beta$ never chooses $\mathrm{none}$;
--   3. $\beta$ is lazy: after a request $q$ whose pickup $q_1$ is occupied, it serves from $q_1$ with probability $1$.
--
--   Then there is a memoryless policy $A$ such that $\beta_A$ and $\beta$ agree at every legal position.
--
--   Together with the bridge, this identifies the platform's memoryless policies with the AJ behaviour strategies of this form.
-- source:
--   New statement introduced by this mission (no prior source); converse of AJOnline.KTaxi2.bridge; laziness as in C. Coester, Y. Huang, T.-Y. Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Appendix C

import Mathlib
import Definitions.Def_AJOnline_KTaxi2

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- **Converse bridge.** A behaviour strategy on the 2-taxi game that, at legal positions, depends
only on (current configuration, last move), never stops after a request, and is lazy (serves from
the pickup when a taxi already stands there) agrees at every legal position with a memoryless
policy read as a behaviour strategy. -/
theorem converse_bridge (x₀ : Fin 2 → ℝ) (β : BehStrategy (game x₀))
    (hdep : ∀ s ∈ (game x₀).pos, ∀ t ∈ (game x₀).pos,
      cfg (locations x₀) s = cfg (locations x₀) t → s.getLast? = t.getLast? → β.next s = β.next t)
    (hstop : ∀ s ∈ (game x₀).pos, ∀ q, s.getLast? = some (Mv.req q) → β.next s none = 0)
    (hlazy : ∀ s ∈ (game x₀).pos, ∀ q, s.getLast? = some (Mv.req q) →
      q.1 ∈ cfg (locations x₀) s → β.next s = PMF.pure (some (Mv.serve q.1))) :
    ∃ A : MemorylessPolicy, ∀ s ∈ (game x₀).pos, (behOf A x₀).next s = β.next s := by sorry

end AJOnline.KTaxi2
