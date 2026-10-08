-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_lemma_4_1
-- name    : BoundedDegreeST.PlusOne.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:46.421079+00:00
-- url     : https://prove2.me/theorems/aa1d91fd-8b0a-4b5e-ab50-cc3363541834
-- title:
--   Lemma 4.1 — a 1-edge or a removable degree constraint
-- statement:
--   Let $x^*$ be a basic feasible solution of LP-MBDCT in a well-formed, nonterminal instance, and let $E^*$ be its support. Then at least one of the following holds:
--
--   $$
--   \exists e\in E:\ x^*_e=1,\qquad\text{or}\qquad
--   \exists w\in W:\ \deg_{E^*}(w)\le B_w+1.
--   $$
--
--   This guarantees that an iteration of the rounding algorithm can change its state.
--
--   **Formalization Note** The forest is required not to be a spanning tree, since Figure 4 would already have returned at Step 1.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 666, Lemma 4.1

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.1, p. 666. -/
theorem lemma_4_1 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    (∃ e ∈ I.E, x e = 1) ∨
    (∃ w ∈ I.W, (degree (support I.E x) w : ℤ) ≤ I.B w + 1) := by sorry
end BoundedDegreeST.PlusOne
