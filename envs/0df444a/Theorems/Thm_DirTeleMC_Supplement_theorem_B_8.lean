-- Prove2me | Theorems.Thm_DirTeleMC_Supplement_theorem_B_8
-- name    : DirTeleMC.Supplement.theorem_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:47:03.296961+00:00
-- url     : https://prove2.me/theorems/a80306eb-e163-45f7-acef-ce3abec9d104
-- title:
--   Theorem B.8 — DB-DST solutions of $G_\theta$ and CONVERT: $\mathrm{OPT}\le\theta$ gives a solution, a $\beta$-violating arborescence a schedule of length $\le\beta\theta$
-- statement:
--   Let $(G,s,K)$ be a DTM instance (all $k=|K|$ terminals are to be informed) and $\theta\ge1$.
--
--   1. If $\mathrm{OPT}\le\theta$, then the time-expanded digraph $G_\theta$ has a solution of DB-DST: an out-arborescence rooted at $(s,0)$ that contains all sinks and respects all degree bounds.
--   2. If $A'$ is an out-arborescence of $G_\theta$ rooted at $(s,0)$ that contains all sinks and in which every call node has at most $\beta\ge1$ children, then $\mathrm{CONVERT}(A')$ is a valid schedule informing all terminals of length at most
--   $$\beta\theta,$$
--   and it is computed in polynomial time.
--   3. In particular, if $s\notin K$ and $K\neq\emptyset$, then $\mathrm{OPT}$ is the least $\theta\ge1$ for which $G_\theta$ has a solution.
--
--   The theorem reduces directed telephone multicast to degree-bounded directed Steiner tree: any DB-DST algorithm that violates the degree bounds by a factor $\beta$ yields a $\beta$-approximation for DTM (Corollary B.9).
--
--   **Formalization Note** Part 3 is stated as: $\theta$ is the least $\theta\ge1$ with a solution iff $\theta$ is the least length of a valid schedule informing all terminals. Polynomial time is a Turing machine (Mathlib `TM2ComputableInTime`) running in time at most $(m+2)^c$ on the encoding of $(G,\theta,A')$, whose output is a run of CONVERT on every input as in 2.
--
--   Differences from the source:
--   - generalization: a DTM instance (s ∉ K, all terminals reachable from s) → parts 1–3 for every instance with k = |K|, without s ∉ K or reachability; reason: the proof uses neither; the statement specializes to the source's instances
--   - reading: In particular, OPT is the least θ for which Gθ has a solution → for s ∉ K and K ≠ ∅: θ is the least θ ≥ 1 with a DB-DST solution iff θ is the least length of a valid schedule informing all terminals; reason: the clause needs OPT ≥ 1, which the source's setting gives (K ⊆ V \ {s}, k ≥ 1; cf. "n, k ≥ 1", p.35); without a terminal OPT = 0 while G_1 already has a solution
--   - reading: CONVERT(A′) is a schedule → every output of CONVERT on A′ is a valid schedule that informs all terminals; reason: Algorithm 3 outputs "a schedule that informs all terminals" and the proof shows it is valid
--   - encoding: CONVERT, with ties in τ unspecified → the relation ConvertRun over every order of children with equal τ; reason: the bound is claimed for every tie order
--   - encoding: computed in polynomial time (in the size of Gθ) → Turing.TM2ComputableInTime from encConv (instance, θ, membership bit and parent of every node of Gθ) to encSched with time ≤ (m + 2)^c; reason: the input length and the size of Gθ are polynomially related
--   - encoding: OPT, the minimum number of rounds of a feasible schedule → comparison with every valid schedule that informs all terminals; reason: no minimum over a possibly empty set is taken; same instances and same bound
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem B.8, p.34 (PDF p.35); proof pp.34–35 (PDF pp.35–36); Definition B.7, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_Supplement_ConvertRun

namespace DirTeleMC.Supplement

open DirTeleMC OnlineCRS.Combine

/-- **Theorem B.8** (the time-expanded digraph and CONVERT).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem B.8, p.34 (proof pp.34–35): "Let θ ≥ 1. (i) If OPT ≤ θ, then Gθ has a
solution of DB-DST, that is, an out-arborescence rooted at (s, 0) that contains all sinks and respects all degree
bounds. (ii) If A′ is an out-arborescence of Gθ rooted at (s, 0) that contains all sinks and in which every call node
has at most β ≥ 1 children, then CONVERT(A′) is a schedule of length at most βθ, computed in polynomial time. In
particular, OPT is the least θ for which Gθ has a solution."

For every DTM instance (`k = |K|`):
1. for every `θ ≥ 1`, if some valid schedule of length at most `θ` informs all terminals, then `G_θ` has a DB-DST
   solution;
2. for every `θ ≥ 1`, every real `β ≥ 1` and every out-arborescence `A′` of `G_θ` rooted at `(s, 0)` that contains all
   sinks and in which every call node has at most `β` children, every output of CONVERT on `A′` is a valid schedule
   that informs all terminals and has at most `β θ` rounds;
3. there is a constant `c` and a Turing machine that, in time at most `(m + 2)^c` on inputs of length `m`, computes
   from the encoding of `(G, θ, A′)` an output of CONVERT on `A′`, whenever `θ ≥ 1` and `A′` is as in 2;
4. if `s ∉ K` and `K ≠ ∅`, then a number `θ` is the least `θ ≥ 1` for which `G_θ` has a DB-DST solution exactly when
   it is the least length of a valid schedule that informs all terminals (OPT).

**Formalization Note.** OPT is written through valid schedules informing all terminals (DTM: `k = |K|`). Machine
model: Mathlib's `Turing.TM2ComputableInTime` over the published alphabet `Fin 4`, inputs encoded by `encConv`,
outputs by `encSched`. The machine of 3 is required to output a run of CONVERT only on inputs as in 2. Part 4 needs
`OPT ≥ 1`, i.e. a terminal other than `s`, which the source's setting provides (`K ⊆ V ∖ {s}`, `k ≥ 1`). -/
theorem theorem_B_8 :
    (∀ I : Inst, I.k = I.K.card → ∀ θ : ℕ, 1 ≤ θ →
      (∃ S : Schedule I.n, S.Valid I ∧ S.InformsK I ∧ S.length ≤ θ) → HasDBDSTSol I θ) ∧
    (∀ I : Inst, I.k = I.K.card → ∀ θ : ℕ, 1 ≤ θ → ∀ β : ℝ, 1 ≤ β → ∀ A : TEArb I.n,
      A.IsOutArbSinks I θ →
      (∀ v t, TENode.call v t ∈ A.verts → ((A.children I (TENode.call v t)).card : ℝ) ≤ β) →
      ∀ S : Schedule I.n, ConvertRun I θ A S →
        S.Valid I ∧ S.InformsK I ∧ (S.length : ℝ) ≤ β * θ) ∧
    (∃ c : ℕ, ∃ alg : ConvInput → List (List (ℕ × ℕ)),
      (∃ M : Turing.TM2ComputableInTime encConv encSched alg, ∀ m, M.time m ≤ (m + 2) ^ c) ∧
      ∀ X : ConvInput, X.I.k = X.I.K.card → 1 ≤ X.θ → X.A.IsOutArbSinks X.I X.θ →
        ∃ S : Schedule X.I.n, alg X = S.toNat ∧ ConvertRun X.I X.θ X.A S) ∧
    (∀ I : Inst, I.k = I.K.card → I.s ∉ I.K → I.K.Nonempty → ∀ θ : ℕ,
      IsLeast {θ' : ℕ | 1 ≤ θ' ∧ HasDBDSTSol I θ'} θ ↔
        IsLeast {L : ℕ | ∃ S : Schedule I.n, S.Valid I ∧ S.InformsK I ∧ S.length = L} θ) := by sorry

end DirTeleMC.Supplement
