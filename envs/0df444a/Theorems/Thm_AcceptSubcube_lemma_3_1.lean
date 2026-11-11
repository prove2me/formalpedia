-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_3_1
-- name    : AcceptSubcube.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:22.585471+00:00
-- url     : https://prove2.me/theorems/a0e6215f-e4f8-411f-8b43-efc84798d3b9
-- title:
--   Lemma 3.1 — enumeration of cheap assignments of a complete instance
-- statement:
--   Let $\ell\ge2$ and let $\mathcal I$ be a complete Boolean $\ell$-CSP on $m$ variables whose predicates each reject at least one pattern. For every integer $K\ge0$:
--
--   1. the family $F_K$ of assignments of cost at most $K$ has VC dimension at most $v_\ell(K)$;
--   2. $|F_K|\le\Sigma(m,v_\ell(K))$;
--   3. $F_K$ can be enumerated in time $m^{O_\ell(1+K^{1/\ell})}$: there are a constant $C$ (depending on $\ell$) and one machine that, on input $(\mathcal I,K)$, outputs a duplicate-free list of exactly the assignments of cost at most $K$ within $(m+2)^{\lceil C(1+K^{1/\ell})\rceil}$ steps;
--   4. satisfiability is decided with a witness in deterministic polynomial time: a polynomial-time machine returns a satisfying assignment when one exists and reports unsatisfiability otherwise.
--
--   The lemma supplies the seeds of the recovery procedure and the exact branch of the algorithm.
--
--   Differences from the source:
--   - reading: enumerated in m^{O_ℓ(1+K^{1/ℓ})} time → one TM2 machine on (I, K), K in binary, halting within (m+2)^{⌈C(1+K^{1/ℓ})⌉} steps on the lemma's instances, C depending on ℓ; reason: the paper names no machine model; base m + 2 covers m ≤ 1
--   - reading: satisfiability is decided, with a witness, in deterministic polynomial time → a TM2 polynomial-time map to "none" or a satisfying assignment, correct on the lemma's instances; reason: machine model reading of "deterministic polynomial time"
--   - encoding: VC dimension of F_K → Mathlib Finset.vcDim of F_K viewed as a set family (each vector by its set of ones); reason: shattering of a coordinate set is the same notion
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.1, p.12

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_FK
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube

/-- **Lemma 3.1 (Enumeration).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.1, p.12: "In a complete Boolean ℓ-CSP on
m variables whose predicates each reject at least one pattern, F_K has VC dimension at most v_ℓ(K)
and size at most Σ(m, v_ℓ(K)), and it can be enumerated in m^{O_ℓ(1+K^{1/ℓ})} time. In particular
satisfiability is decided, with a witness, in deterministic polynomial time."

Four clauses, for every arity `ℓ ≥ 2`: the VC bound, the size bound, an enumerator (output: a list
without repetitions of exactly the assignments of cost `≤ K`) running within
`(m + 2)^{⌈C(1 + K^{1/ℓ})⌉}` steps for a constant `C` depending on `ℓ`, and a deterministic
polynomial-time satisfiability test returning a satisfying assignment when one exists.

**Formalization Note.** `ℓ ≥ 2` is §3's standing arity (p.11). VC dimension is Mathlib's
`Finset.vcDim` of the family as a set family (`toSets`). `m^{O_ℓ(1+K^{1/ℓ})}` is read with base
`m + 2` (so that `m ≤ 1` is covered); the machine reads `(I, K)` with `K` in binary, and the bound
is required on the lemma's instances. -/
theorem lemma_3_1 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (∀ I : GInst, I.IsComplete ℓ → I.RejectsSome → ∀ K : ℕ,
        (toSets (FK I K)).vcDim ≤ vl ℓ K ∧ (FK I K).card ≤ sigmaSum I.n (vl ℓ K)) ∧
    (∃ (C : ℝ) (enum : GInst × ℕ → List (List Bool)),
        ComputesWithinOn (fun x : GInst × ℕ => x.1.IsComplete ℓ ∧ x.1.RejectsSome)
          encInstNat encAssignList enum
          (fun x => (x.1.n + 2) ^ ⌈C * (1 + (x.2 : ℝ) ^ ((1 : ℝ) / ℓ))⌉₊) ∧
        ∀ I : GInst, I.IsComplete ℓ → I.RejectsSome → ∀ K : ℕ,
          (enum (I, K)).Nodup ∧ (∀ y ∈ enum (I, K), y.length = I.n) ∧
          ∀ x : Fin I.n → Bool, List.ofFn x ∈ enum (I, K) ↔ cost I x ≤ K) ∧
    (∃ sat : GInst → Option (List Bool),
        Nonempty (Turing.TM2ComputableInPolyTime encInst encOptAssign sat) ∧
        ∀ I : GInst, I.IsComplete ℓ → I.RejectsSome →
          ((∃ x : Fin I.n → Bool, cost I x = 0) →
              ∃ y, sat I = some y ∧ y.length = I.n ∧ cost I (asg I y) = 0) ∧
          ((∀ x : Fin I.n → Bool, cost I x ≠ 0) → sat I = none)) := by sorry

end AcceptSubcube
