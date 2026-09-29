-- Prove2me | Theorems.Thm_BertsekasDP_label_correcting_invariant
-- name    : BertsekasDP.label_correcting_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-06T05:30:04.031225+00:00
-- url     : https://prove2.me/theorems/ba1708ba-c5de-484b-8450-54858d593f87
-- title:
--   Labels are walk lengths (invariant)
-- statement:
--   **The label invariant of the label correcting method** (Bertsekas, Vol. I, §2.3.1, stated in the text preceding Prop. 2.3.1). At every state $\sigma$ reachable from the initial state — after any number of iterations, with any removal order — the labels are not arbitrary numbers but lengths of actual walks:
--
--   1. for every node $j$, either $d_j = +\infty$, or there is a walk $l$ from the origin $s$ to $j$ with
--   $$d_j \;=\; \ell(l);$$
--   2. either $\mathrm{UPPER} = +\infty$, or there is a walk $l$ from $s$ to the destination $t$ with $\mathrm{UPPER} = \ell(l)$.
--
--   Neither claim asserts optimality: the exhibited walk need not be shortest. What the invariant provides is the "$\ge$" half of correctness — since $\mathrm{UPPER}$ is always the length of some genuine $s \to t$ walk, it can never fall below $\operatorname{dist}(s,t)$ — and it is also the engine of the termination argument, which counts the possible label values.
--
--   **Formalization Note** No hypothesis on arc or cycle lengths is needed here; the invariant holds for arbitrary real lengths. In the second disjunct the label is a coerced real number, so the statement also records that a non-infinite label is finite (never $-\infty$). For $j = s$ the one-element walk $(s)$, of length $0$, is among the witnesses.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 2.3.1 (in-text invariant)

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_BertsekasLCState

namespace BertsekasDP

theorem label_correcting_invariant {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (σ : BertsekasLCState V)
    (hreach : Relation.ReflTransGen (BertsekasLCStep G) (BertsekasLCInit G) σ) :
    (∀ j : V, σ.label j = ⊤ ∨
      ∃ l, BertsekasIsWalkFrom G G.s j l ∧
        σ.label j = (BertsekasWalkLength G l : EReal)) ∧
    (σ.upper = ⊤ ∨
      ∃ l, BertsekasIsWalkFrom G G.s G.t l ∧
        σ.upper = (BertsekasWalkLength G l : EReal)) := by sorry

end BertsekasDP
