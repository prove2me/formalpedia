-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_2_3_meta_theorem
-- name    : ContractionLemma.Supplement.theorem_2_3_meta_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:21:07.205869+00:00
-- url     : https://prove2.me/theorems/959498b4-1587-4b6b-a232-0db4cf623c4e
-- title:
--   Theorem 2.3, p.17 — meta-theorem: an $(s,q,H)$-tensor-preserving reduction gives an algorithm in time $H+q\,\mathrm{poly}(L+s)E(s)$
-- statement:
--   Let $\Pi$ be a problem, a relation between instances and admissible answers, and let $s,q,H$ be functions of the input length $L$. Suppose $R$ is an $(s,q,H)$-tensor-preserving reduction for $\Pi$ (Definition 2.2) with entry machine $E$ and constant $c$. Then there are an algorithm $A$ and a constant $C$ such that, on every instance $x$ with $L=|x|$ and $s=s(L)$, $q=q(L)$,
--
--   $$
--   \text{time}\;\le\;H(L)+q\cdot C(L+s+1)^C\,2^{C s/\sqrt{\log_2(s+2)}},\qquad \text{space}\;\le\;C(L+s+1)^C .
--   $$
--
--   1. If the reduction is deterministic, $A$ is deterministic and always returns an admissible answer.
--   2. If the reduction is randomized with error bound $\delta(x)$, $A$ is randomized and returns an inadmissible answer on $x$ with probability at most $\delta(x)$.
--
--   Every algorithm of the paper is a tensor-preserving reduction followed by this theorem.
--
--   Differences from the source:
--   - reading: "an algorithm that … computes the answer from the values $Z(G_1),\dots,Z(G_q)$" (no oracle mechanics) → an oracle machine: the query is the clean word $I$ on the query tape, the reply $Z(G)\in R_{P,\ell}$ replaces the reply tape, one step per query; reason: Definition 2.2 does not say how the values are obtained
--   - encoding: (iv) "an entry algorithm" → one fixed entry machine $E$ of the reduction, reading the base-mission instance description; reason: the base mission's reading of entry algorithms
--   - reading: "a randomized reduction keeps its error bound" → fair coins read one at a time on request (an oracle step with an empty query, one step and one visited cell per coin; coin requests do not count among the $q$ queries); the error is the fraction of coin strings in $\{0,1\}^{\lceil\tau\rceil}$ giving an inadmissible answer, and the randomized algorithm uses the same coin model; reason: the paper does not define randomized reductions; this is the coin model of §2.5 (p.20)
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 2.3 and Definition 2.2, p.17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Reduction

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **Theorem 2.3 (Meta-theorem)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.17 (PDF p.20).

"An `(s, q, H)`-tensor-preserving reduction for `Π` gives an algorithm for `Π` with running time
`H + q · poly(L + s) E(s)` and space `poly(L + s)`. A deterministic reduction gives a deterministic
algorithm, and a randomized reduction keeps its error bound."

For every problem `Π` (a relation between instances and admissible answers), scale, query and time
functions `s, q, H` of the input length `L`, and every reduction (oracle machine `R`, entry machine
`E`, constant `c`), there are a machine `A` and a constant `C` with:

1. if the reduction is deterministic (`IsDetReduction`), then `A` computes an admissible answer on
   every instance in time `H(L) + q(L)·C (L+s+1)^C 2^{C s/√log₂(s+2)}` and space `C (L+s+1)^C`;
2. for every error bound `δ`, if the reduction is randomized with error at most `δ(x)` on every
   instance `x` (`IsRandReduction`), then `A` is a randomized algorithm with the same time and space
   bounds whose probability of returning an inadmissible answer on `x` is at most `δ(x)`.

**Formalization Note.** Oracle access (`OracleMachine`) and the conditions (i)–(iv) of Definition 2.2
(`contractionReply`) are a declared reading: the paper defines no oracle mechanics. Randomized
reductions and algorithms read fair coins on request, one-way, as the §2.5 coin model
(`RandORunsWithin`, `RandRunsWithin`); the randomized algorithm `A` is a machine with coin requests
and no other oracle. `E(s)` is
`2^{C f(s)}`, `f(s) = s/√log₂(s+2)` (p.16). Each of the two parts has its own machine `A`. -/
theorem theorem_2_3_meta_theorem
    (Prob : List Bool → List Bool → Prop) (s q : ℕ → ℕ) (H : ℕ → ℝ)
    (R : OracleMachine) (outR : Fin R.machine.tapeCount)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (c : ℕ) :
    (IsDetReduction Prob s q H R outR E outE c →
      ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ), ∀ x : List Bool, ∃ y, Prob x y ∧
        ContractionLemma.RunsWithin A outA x y
          (H x.length + q x.length * (C * ((x.length : ℝ) + s x.length + 1) ^ C *
            (2 : ℝ) ^ (C * fScale (s x.length))))
          (C * ((x.length : ℝ) + s x.length + 1) ^ C)) ∧
    (∀ δ : List Bool → ℝ, IsRandReduction Prob s q H R outR E outE c δ →
      ∃ (A : OracleMachine) (outA : Fin A.machine.tapeCount) (C : ℕ), ∀ x : List Bool,
        A.RandRunsWithin outA x
          (H x.length + q x.length * (C * ((x.length : ℝ) + s x.length + 1) ^ C *
            (2 : ℝ) ^ (C * fScale (s x.length))))
          (C * ((x.length : ℝ) + s x.length + 1) ^ C) (fun _ => True) (Prob x) (δ x)) := by sorry

end ContractionLemma.Supplement
