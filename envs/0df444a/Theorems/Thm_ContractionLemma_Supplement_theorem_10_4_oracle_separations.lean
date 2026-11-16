-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_10_4_oracle_separations
-- name    : ContractionLemma.Supplement.theorem_10_4_oracle_separations
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:30:41.194224+00:00
-- url     : https://prove2.me/theorems/2ca84749-4d0e-4b42-9691-5a10741f24db
-- title:
--   Theorem 10.4, p.42 — oracle separations: $\mathsf E\not\subseteq\mathsf{DTIME}[t]^A$, $\mathsf{NE}\not\subseteq\mathsf{NTIME}[t]^A$, and $\mathsf E\not\subseteq\mathsf{NTIME}[n]^A$ with short queries
-- statement:
--   For every $t$ in the range (1):
--
--   1. **(a)** $\mathsf E\not\subseteq\mathsf{DTIME}[t]^A$ and $\mathsf{NE}\not\subseteq\mathsf{NTIME}[t]^A$, uniformly over all oracles $A$ in $\mathcal C^{cl}_n$ and for $A=\mathsf{MINKT}_U$, with adaptive queries of length $O(t)$: a single language in $\mathsf E$ (resp. $\mathsf{NE}$) lies outside $\mathsf{DTIME}[t]^A$ (resp. $\mathsf{NTIME}[t]^A$) for all these oracles at once;
--   2. **(b)** $\mathsf E\not\subseteq\mathsf{NTIME}[n]^A$ with queries of length $O(n^{9/10})$, uniformly over all oracles $A$ decidable in time $2^{O(m)}$ and space $\mathrm{poly}(m)$;
--   3. such oracles include TQBF and MKTP: both are decidable in time $2^{O(m)}$ and space $\mathrm{poly}(m)$.
--
--   The oracles in (b) need not be fast, because each short query is answered inside one block of the simulation.
--
--   Differences from the source:
--   - reading: "uniformly over all oracles $A$" → one language outside the union of the oracle classes over all those $A$; reason: the proof applies Lemma 2.12 "to the union over all such oracles" (p.42)
--   - generalization: $A=\mathsf{MINKT}_U$ for a fixed universal $U$ → $A=\mathsf{MINKT}_U$ for every deterministic local machine $U$; reason: the proof uses only Theorem 3, which holds for every such $U$; a universal $U$ is a special case
--   - generalization: "unrestricted MKTP" (for a universal machine) → MKTP for every deterministic B.2 machine $U$ with $\mathrm{KT}_U(x)\le c(|x|+1)$ for all $x$; reason: the proof uses only "the literal description gives $\mathrm{KT}(x)=O(|x|)$" (p.42), which a universal machine satisfies
--   - encoding: time $O(t)$ (clocks $c\,t(n)$, at most $c\,t(n)$ gates, ancillas and witness bits; time-constructibility within $O(t(n))$ steps) → $c\,(t(n)+1)$; reason: equal to $c\,t(n)$ up to the constant for $n\ge1$, since $t(n)\ge n\ge1$; at $n=0$ it avoids the junk bound $0$, under which no machine halts and $t(n)=n$ would not be time-constructible
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 10.4, p.42; Definitions 2.10, 2.11, p.21; App. B.2, p.103

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Quantum
import Definitions.Def_ContractionLemma_Supplement_Classes
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 10.4 (Oracle separations)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.42 (PDF p.45).

"For every `t` in the range (1):
(a) `E ⊄ DTIME[t]^A` and `NE ⊄ NTIME[t]^A`, uniformly over all oracles `A` in `C^cl_n` and for
`A = MINKT_U`, with adaptive queries of length `O(t)`;
(b) `E ⊄ NTIME[n]^A` with queries of length `O(n^{9/10})`, uniformly over all oracles `A` decidable
in time `2^{O(m)}` and space `poly(m)`, such as TQBF and unrestricted MKTP."

For every `t` in the range (1):

1. some language in E is in no `DTIME[t]^A`, and some language in NE in no `NTIME[t]^A`, where `A`
   ranges over the languages of `C^cl_n` and the `MINKT_U` of all deterministic local machines `U`;
2. some language in E is in no `NTIME[n]^A` with queries of length `O(n^{9/10})`, where `A` ranges
   over the languages decidable in time `2^{O(m)}` and space `poly(m)`;
3. TQBF is decidable in time `2^{O(m)}` and space `poly(m)`, and so is MKTP for every deterministic
   B.2 machine `U` that describes every `x` within `KT(x) ≤ c(|x|+1)`.

**Formalization Note.** "Uniformly over all oracles" is read as one language outside the union over
all those oracles. The paper's universal `U` is replaced by the property its proof uses: for MINKT
every deterministic `U` (a generalization), for MKTP every `U` with `KT(x) = O(|x|)` ("the literal
description gives `KT(x) = O(|x|)`", p.42). Queries of an `O(t)`-time machine have length `O(t)`
automatically. -/
theorem theorem_10_4_oracle_separations (t : ℕ → ℕ) (ht : Range1 t) :
    (∃ L : Lang, InE L ∧ ∀ A : Lang,
      (InCcl (fun n => n) A ∨ ∃ (p : LocalParams) (U : LProgram p), U.IsDet ∧ A = MINKT U) →
      ¬ DTIMEo t A L) ∧
    (∃ L : Lang, InNE L ∧ ∀ A : Lang,
      (InCcl (fun n => n) A ∨ ∃ (p : LocalParams) (U : LProgram p), U.IsDet ∧ A = MINKT U) →
      ¬ ClClass .N t A L) ∧
    (∃ L : Lang, InE L ∧ ∀ A : Lang, ExpTimePolySpace A →
      ¬ NTIMEoQ (fun n => n) (fun n => (n : ℝ) ^ ((9 : ℝ) / 10)) A L) ∧
    ExpTimePolySpace TQBF ∧
    ∀ (p : LocalParams) (U : LProgram p) (c : ℕ), U.IsDet →
      (∀ x : List Bool, ∃ (d : List Bool) (t' : ℕ), d.length + t' ≤ c * (x.length + 1) ∧
        Describes U x d t') →
      ExpTimePolySpace (MKTP U) := by sorry

end ContractionLemma.Supplement
