-- Prove2me | Theorems.Thm_ContractionLemma_theorem_A_2_contraction_lemma_mod
-- name    : ContractionLemma.theorem_A_2_contraction_lemma_mod
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:13.632205+00:00
-- url     : https://prove2.me/theorems/0bc7f146-a0ba-4391-91fc-fe109aea2d75
-- title:
--   Theorem A.2 — the contraction lemma for entries modulo $2^P$
-- statement:
--   For every constant $c$ and every entry machine $E$ there are a machine $A$ and a constant $C$ such that the following holds for every instance with scale $s$ and input length $N$. Suppose the network $G$ has at most $cs$ edges and maximum degree at most $cs^{9/10}$, that $1\le P\le cs$, and that its tables, with entries integers modulo $2^P$, are computed by $E$ in time $c(N+s+1)^c2^{cs^{9/10}}$ and space $c(N+s+1)^c$. Then $A$ on the encoded instance halts with $Z(G)\bmod 2^P$ on its output tape, in time
--
--   $$
--   C(N+s+1)^C\,2^{Cs/\sqrt{\log_2(s+2)}}
--   $$
--
--   and in space $C(N+s+1)^C$ at every step.
--
--   This is the form the appendix of the paper proves; the extension to truncated polynomial entries is the main theorem of the mission.
--
--   **Formalization Note** Same machine model, encodings and quantifier order as Theorem 2.1. The field $\ell$ of an instance is not used.
--
--   Differences from the source:
--   - reading: a description of length poly(N + s), each entry computable within the stated cost → the explicit edge list as part of the input, and a fixed entry machine run on (instance, v, bits), quantified before A; reason: the paper leaves the input encoding open, and this is a description of that length
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat
--   - encoding: every O(·) and poly(·) → ∀ c, E ∃ A, C ∀ instances with the explicit expressions; reason: constants may depend only on the constants of the hypotheses
--   - encoding: log s → log₂(s + 2); reason: the paper's own f(u) = u/√log(u+2), p.16; it avoids the junk value at s = 1
--   - encoding: an input from which G is produced, with P → an Instance, whose field ℓ is not used by this statement; reason: the same input type as Theorem 2.1; every source instance is an instance (any ℓ), so no case is lost
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem A.2, pp.49–50

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Instance

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem A.2 (Contraction lemma)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), pp.49–50 (PDF pp.52–53).

The contraction lemma for entries that are integers modulo `2^P` (the case `ℓ = 1` of
Theorem 2.1): for every `c` and every entry machine `E` there are a machine `A` and a constant
`C` such that, for every instance with at most `c·s` edges, maximum degree at most
`c·s^{9/10}`, `1 ≤ P ≤ c·s`, and tables in `ℤ/2^Pℤ` computed by `E` in time
`c (N+s+1)^c 2^{c s^{9/10}}` and space `c (N+s+1)^c`, the machine `A` outputs `Z(G) mod 2^P`
(as an integer in `[0, 2^P)`, in binary) in time `C (N+s+1)^C 2^{C s/√(log₂(s+2))}` and space
`C (N+s+1)^C`.

**Formalization Note.** Same machine model, encodings and quantifier order as
`theorem_2_1_contraction_lemma`; the field `ℓ` of the instance is not used. -/
theorem theorem_A_2_contraction_lemma_mod :
    ∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
    ∀ (I : Instance) (T : I.Tables (ZMod (2 ^ I.P))),
      1 ≤ I.P → I.P ≤ c * I.s → I.m ≤ c * I.s →
      (I.maxDeg : ℝ) ≤ c * (I.s : ℝ) ^ ((9 : ℝ) / 10) →
      I.EntryComputesMod E outE T
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c * (2 : ℝ) ^ (c * (I.s : ℝ) ^ ((9 : ℝ) / 10)))
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c) →
      RunsWithin A outA I.encode (countWord (I.net T).Z.val)
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C *
          (2 : ℝ) ^ (C * (I.s : ℝ) / Real.sqrt (Real.logb 2 ((I.s : ℝ) + 2))))
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C) := by sorry

end ContractionLemma
