-- Prove2me | Theorems.Thm_AJOnline_KTaxi2_bridge
-- name    : AJOnline.KTaxi2.bridge
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:36:27.602872+00:00
-- url     : https://prove2.me/theorems/ba2dda86-e756-4216-b5de-79cb81fc4130
-- title:
--   Bridge: memoryless 2-taxi policies are AJ behaviour strategies with the same costs
-- statement:
--   Let $A$ be a memoryless 2-taxi policy and $x_0$ a labelled start. Then:
--
--   1. the behaviour strategy $\beta_A$ depends on the history only through the pair (current configuration, last move);
--   2. for every finite list $\mathbf q$ of requests, played as the script $\mathrm{req}(q^1),\dots,\mathrm{req}(q^n)$,
--   $$\mathbb E[\mathrm{alg}]=\mathrm{memorylessCost}(A,X_0,\mathbf q),\qquad \mathbb E[\mathrm{opt}]=\mathrm{optCost}_{x_0}(\mathbf q).$$
--
--   These are the platform's expected memoryless cost and offline optimum.
-- source:
--   New statement introduced by this mission (no prior source); the 2-taxi model is that of C. Coester, Y. Huang, T.-Y. Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Appendix C, as formalized in KTaxi.Competitive.Supplement

import Mathlib
import Definitions.Def_AJOnline_KTaxi2

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- **Bridge to the platform's memoryless 2-taxi model.** A `MemorylessPolicy`, read as a behaviour
strategy on the 2-taxi AJ game, depends on the history only through (configuration, last move).
Against the request script `qs` its expected cost is `memorylessCost` and its expected offline optimum
is `optCost`. AJ axioms used: none beyond the definitions (the game's positions satisfy G1–G3 by
construction); no tensor axiom, no deterministic-strategy axiom. -/
theorem bridge (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) :
    (behOf A x₀).DependsOn (fun s => (cfg (locations x₀) s, s.getLast?)) ∧
    ∀ qs : List (ℝ × ℝ),
      expAlg (costed x₀) (behOf A x₀) (qs.map Mv.req) = memorylessCost A (locations x₀) qs ∧
      expOpt (costed x₀) (behOf A x₀) (qs.map Mv.req) = optCost x₀ qs := by sorry

end AJOnline.KTaxi2
