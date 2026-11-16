-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_5_circuit_counting
-- name    : ContractionLemma.Supplement.theorem_5_circuit_counting
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:24:12.451652+00:00
-- url     : https://prove2.me/theorems/ef84d005-453b-4698-b2e8-214ed3686c3e
-- title:
--   Theorem 5, p.27 — counting satisfying inputs of a fan-in-two circuit in time $\mathrm{poly}(L)E(s+n)$
-- statement:
--   Let $C$ be a fan-in-two circuit of size $s$ on $n$ inputs, with one output gate, and let $L$ be the length of its description. Then each of the following can be computed deterministically in time $\mathrm{poly}(L)\,E(s+n)$ and polynomial space:
--
--   1. the number $\#C$ of satisfying inputs of $C$;
--   2. its exact acceptance probability $\#C/2^n$;
--   3. a satisfying input, or the report that there is none.
--
--   In particular, for every constant $c$, #SAT and exact CAPP for circuits of size at most $c\,n$ take time $2^{O_c(n/\sqrt{\log n})}$.
--
--   The bounds are $C(L+1)^C\,2^{C(s+n)/\sqrt{\log_2(s+n+2)}}$ in time and $C(L+1)^C$ in space, and $C'\,2^{C'n/\sqrt{\log_2(n+2)}}$ in time for size at most $c\,n$, $C'$ depending on $c$.
--
--   Differences from the source:
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: the circuit accepts when its output gate is 1 → a well-formed circuit with exactly one designated output wire; reason: Lean form of "its output gate"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 5, p.27 (stated first on p.5); §2.3, p.18

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped Classical
/-- **Theorem 5 (Circuit counting)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.27 (PDF p.30; stated first on p.5).

"Let `C` be a fan-in-two circuit of size `s` on `n` inputs. The number of satisfying inputs of `C`,
and hence its exact acceptance probability, can be computed in time `poly(L) E(s + n)`, and a
satisfying input can be found within the same bound. In particular, for every constant `c`, #SAT and
exact CAPP for circuits of size `cn` take time `2^{O_c(n/√log n)}`."

For well-formed single-output circuits (`L` the length of the encoding), there are machines and a
constant `C` that compute, in time `C (L+1)^C 2^{C f(s+n)}` and space `C (L+1)^C`:

1. the number of satisfying inputs (output `1`);
2. the acceptance probability `#sat / 2^n`, as a rational;
3. a satisfying input, or `none` when there is none;

and, for every `c`, a constant `C'` such that the first two machines run in time `C' 2^{C' f(n)}` on
circuits of size at most `c·n`.

**Formalization Note.** `f(u) = u/√log₂(u+2)`. The polynomial-space clause is the paper's
convention (p.3). -/
theorem theorem_5_circuit_counting :
    ∃ (A₁ : PrimitiveMachine) (out₁ : Fin A₁.tapeCount) (A₂ : PrimitiveMachine)
      (out₂ : Fin A₂.tapeCount) (A₃ : PrimitiveMachine) (out₃ : Fin A₃.tapeCount) (C : ℕ),
    (∀ Ck : FCircuit, Ck.WellFormed → Ck.outs.length = 1 →
      ContractionLemma.RunsWithin A₁ out₁ Ck.encode
        (countWord (Finset.univ.filter fun x : Fin Ck.nIn → Bool =>
          Ck.eval (List.ofFn x) = [true]).card)
        (C * ((Ck.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale (Ck.size + Ck.nIn)))
        (C * ((Ck.encode.length : ℝ) + 1) ^ C) ∧
      ContractionLemma.RunsWithin A₂ out₂ Ck.encode
        (ratWord ((Finset.univ.filter fun x : Fin Ck.nIn → Bool =>
          Ck.eval (List.ofFn x) = [true]).card / 2 ^ Ck.nIn))
        (C * ((Ck.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale (Ck.size + Ck.nIn)))
        (C * ((Ck.encode.length : ℝ) + 1) ^ C) ∧
      ∃ o : Option (Fin Ck.nIn → Bool),
        (match o with
          | none => ∀ x : Fin Ck.nIn → Bool, Ck.eval (List.ofFn x) ≠ [true]
          | some x => Ck.eval (List.ofFn x) = [true]) ∧
        ContractionLemma.RunsWithin A₃ out₃ Ck.encode (optWord (o.map vecWord))
          (C * ((Ck.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale (Ck.size + Ck.nIn)))
          (C * ((Ck.encode.length : ℝ) + 1) ^ C)) ∧
    ∀ c : ℕ, ∃ C' : ℕ, ∀ Ck : FCircuit, Ck.WellFormed → Ck.outs.length = 1 →
      Ck.size ≤ c * Ck.nIn →
      RunsInTime A₁ out₁ Ck.encode
        (countWord (Finset.univ.filter fun x : Fin Ck.nIn → Bool =>
          Ck.eval (List.ofFn x) = [true]).card)
        (C' * (2 : ℝ) ^ (C' * fScale Ck.nIn)) ∧
      RunsInTime A₂ out₂ Ck.encode
        (ratWord ((Finset.univ.filter fun x : Fin Ck.nIn → Bool =>
          Ck.eval (List.ofFn x) = [true]).card / 2 ^ Ck.nIn))
        (C' * (2 : ℝ) ^ (C' * fScale Ck.nIn)) := by sorry

end ContractionLemma.Supplement
