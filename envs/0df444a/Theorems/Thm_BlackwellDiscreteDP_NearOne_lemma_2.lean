-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_lemma_2
-- name    : BlackwellDiscreteDP.NearOne.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:10.37199+00:00
-- url     : https://prove2.me/theorems/7db57ed7-5c9d-4045-a94d-513cecf86781
-- title:
--   Lemma 2 — g(s) ∈ E(s, f) for all s ⇒ x(g) = x(f); if also Q*(g)Q*(f) = Q*(g), then y(g) = y(f)
-- statement:
--   In the finite decision model, let $f,g\in F$ be such that $g(s)\in E(s,f)$ for every state $s$. Then
--   $$x(g)=x(f).$$
--   If in addition $Q^*(g)Q^*(f)=Q^*(g)$, then $y(g)=y(f)$.
--
--   Lemma 2 shows that switching to tied actions preserves average income, and under the stated compatibility of limit matrices also the bias; it drives the proof of Theorem 4(d).
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 724, Lemma 2

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Lemma 2.** For any `f, g ∈ F` for which `g(s) ∈ E(s, f)` for all `s`, we have
`x(g) = x(f)`. If in addition `Q*(g)Q*(f) = Q*(g)`, then `y(g) = y(f)`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 724, Lemma 2. -/
theorem lemma_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hE : ∀ s, g s ∈ M.gainBiasEqualSet f s) :
    M.x g = M.x f ∧ (M.Qstar g * M.Qstar f = M.Qstar g → M.y g = M.y f) := by sorry

end BlackwellDiscreteDP.NearOne
