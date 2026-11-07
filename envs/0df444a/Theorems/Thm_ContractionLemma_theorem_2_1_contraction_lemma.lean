-- Prove2me | Theorems.Thm_ContractionLemma_theorem_2_1_contraction_lemma
-- name    : ContractionLemma.theorem_2_1_contraction_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:20.383549+00:00
-- url     : https://prove2.me/theorems/b51b2282-82b3-4acd-90be-459f50a0d7b4
-- title:
--   Theorem 2.1 — the contraction lemma over $R_{P,\ell}$
-- statement:
--   For every constant $c$ and every entry machine $E$ there are a machine $A$ and a constant $C$ such that the following holds for every instance with scale $s$ and input length $N$. Suppose the network $G$ has at most $cs$ edges and maximum degree at most $cs^{9/10}$, that $1\le P\le cs$ and $1\le\ell\le cs$, and that its tables, with entries in $R_{P,\ell}=(\mathbb Z/2^P\mathbb Z)[V]/(V^\ell)$, are computed by $E$ in time $c(N+s+1)^c2^{cs^{9/10}}$ and space $c(N+s+1)^c$. Then $A$ on the encoded instance halts with the $\ell$ coefficients of $Z(G)\in R_{P,\ell}$ on its output tape, deterministically and exactly, in time
--
--   $$
--   C(N+s+1)^C\,2^{Cs/\sqrt{\log_2(s+2)}}
--   $$
--
--   and in space $C(N+s+1)^C$ at every step.
--
--   Brute force takes time $2^{\Theta(s)}$. This statement is the common source of the paper's algorithms and lower bounds, and its special case for CNF formulas refutes the Exponential Time Hypothesis.
--
--   **Formalization Note** Every $O(\cdot)$ and $\mathrm{poly}(\cdot)$ is a constant fixed before the instance, so the bound cannot be met by choosing $C$ per instance. The machine $A$ may depend on $c$ and $E$. An entry costs real machine steps, not unit-cost queries.
--
--   Differences from the source:
--   - reading: a description of length poly(L + s), each entry computable within the stated cost → the explicit edge list as part of the input, and a fixed entry machine run on (instance, v, bits), quantified before A; reason: the paper leaves the input encoding open, and this is a description of that length
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat
--   - encoding: every O(·) and poly(·), with L the input length → ∀ c, E ∃ A, C ∀ instances with the explicit expressions, N the encoding length; reason: constants may depend only on the constants of the hypotheses
--   - encoding: log s → log₂(s + 2); reason: the paper's own f(u) = u/√log(u+2), p.16; it avoids the junk value at s = 1
--   - encoding: R_{P,ℓ} as lists of ℓ integers modulo 2^P → polynomials over ZMod (2^P), read through their ℓ low coefficients, output as ℓ binary integers in [0, 2^P); reason: truncation is a ring homomorphism, so the same element of R_{P,ℓ} results
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 2.1, p.16

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Instance

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **Theorem 2.1 (Contraction lemma)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.16 (PDF p.19); its proof is Theorem A.2 with Lemma A.23.

For every constant `c` and every entry machine `E` there are a machine `A` and a constant `C`
such that for every instance `I` (scale `s`, input length `N = |encode I|`) whose network has
at most `c·s` edges and maximum degree at most `c·s^{9/10}`, with `1 ≤ P ≤ c·s` and
`1 ≤ ℓ ≤ c·s`, and whose tables `T` (entries in `R_{P,ℓ}`) are computed by `E` in time
`c (N+s+1)^c 2^{c s^{9/10}}` and space `c (N+s+1)^c`, the machine `A` run on the encoding of
`I` halts with the `ℓ` coefficients of `Z(G) ∈ R_{P,ℓ}` on its output tape, in time
`C (N+s+1)^C 2^{C s / √(log₂(s+2))}` and in space `C (N+s+1)^C` at every step.

**Formalization Note.** Every `O(·)` and `poly(·)` is a constant fixed before the instance
(`∀ c ∀ E ∃ A ∃ C ∀ I T`). The description of the network is the explicit edge list in
`Instance.encode`, so `poly(L + s)` is read as a polynomial in `N + s`. The entry machine is run
on the instance, the vertex and the bits of its edges in increasing edge order (`entryInput`).
`log s` is `log₂(s+2)` (the paper's `f(u) = u/√log(u+2)`, p.16), which avoids the junk value at
`s = 1`. -/
theorem theorem_2_1_contraction_lemma :
    ∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
    ∀ (I : Instance) (T : I.Tables (TruncPoly I.P)),
      1 ≤ I.P → I.P ≤ c * I.s → 1 ≤ I.ℓ → I.ℓ ≤ c * I.s → I.m ≤ c * I.s →
      (I.maxDeg : ℝ) ≤ c * (I.s : ℝ) ^ ((9 : ℝ) / 10) →
      I.EntryComputes E outE T
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c * (2 : ℝ) ^ (c * (I.s : ℝ) ^ ((9 : ℝ) / 10)))
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c) →
      RunsWithin A outA I.encode (truncWord I.ℓ (I.net T).Z)
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C *
          (2 : ℝ) ^ (C * (I.s : ℝ) / Real.sqrt (Real.logb 2 ((I.s : ℝ) + 2))))
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C) := by sorry

end ContractionLemma
