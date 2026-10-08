-- Prove2me | Theorems.Thm_CostScaling_StrongPoly_lemma_4_4_fixedArcs_strict
-- name    : CostScaling.StrongPoly.lemma_4_4_fixedArcs_strict
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:12.755344+00:00
-- url     : https://prove2.me/theorems/84f06f26-28a2-4992-9945-3c9084ab6644
-- title:
--   Lemma 4.4 — reducing ε by 2n strictly enlarges the fixed-arc set
-- statement:
--   Let $G=(V,E)$ be a circulation network with $n=|V|\ge2$ and $m=|E|\ge n-1$. For $ε>0$ and $0\le ε'\le ε/(2n)$, suppose there is an ε-tight circulation. Then the set of fixed arcs grows strictly:
--
--   $$
--   F_ε\subsetneq F_{ε'}.
--   $$
--
--   Every such reduction of the tight error parameter therefore fixes at least one arc that was not fixed before. This is the finite progress measure used in Theorem 4.5.
--
--   **Formalization Note** The printed lemma omits $ε>0$, but without it the claim is false: $ε=ε'=0$ would assert $F_0\subsetneq F_0$. Its proof and Figure 3 use the lemma only at positive ε. The bound $m\ge n-1\ge1$ is the paper's standing network assumption. The set $F_ε$ uses the reused ε-optimality convention, equivalent under $p\mapsto-p$.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 4.4, p. 17; Section 2.1, p. 5; Section 2.2, p. 7

import Mathlib
import Definitions.Def_CostScaling_StrongPoly_IsEpsTight
import Definitions.Def_CostScaling_StrongPoly_fixedArcs

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma 4.4, p. 17: when the error parameter drops by a factor of `2n`, the
set of fixed arcs grows strictly. Positive `ε` is required by the proof and by
the statement's truth at the boundary. -/
theorem lemma_4_4_fixedArcs_strict (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (hscale : ε' ≤ ε / (2 * (Fintype.card V : ℝ)))
    (htight : ∃ f : V → V → ℝ, IsEpsTight N f ε) :
    fixedArcs N ε ⊂ fixedArcs N ε' := by sorry

end CostScaling.StrongPoly
