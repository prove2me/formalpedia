-- Prove2me | Theorems.Thm_DirTeleMC_Supplement_theorem_5_2
-- name    : DirTeleMC.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:46:23.901333+00:00
-- url     : https://prove2.me/theorems/cdd5aee9-259e-49e6-b294-8b78e3099bc0
-- title:
--   Theorem 5.2 — LPSEP on a $p$-root-path separable class computes a DTM schedule of length at most $14\min\{p,k\}(\lfloor\log_2k\rfloor+1)^2\,\mathrm{OPT}$
-- statement:
--   Let $p\ge1$ be an integer and $\mathcal G$ a $p$-root-path separable class: $\mathcal G$ is minor-closed, every connected graph in $\mathcal G$ is $p$-root-path separable, and $Z$ is a deterministic polynomial-time separator algorithm for $\mathcal G$ (Definition 5.1). Run with $Z$, LPSEP is a deterministic polynomial-time algorithm that, given a digraph whose underlying graph lies in $\mathcal G$, a source $s$ and a set $K$ of $k\ge2$ terminals reachable from $s$ with $s\notin K$, computes a valid schedule $S$ informing all terminals with
--   $$|S|\le14\,\min\{p,k\}\,(\bar d+1)^2\,\mathrm{OPT},\qquad \bar d=\lfloor\log_2k\rfloor.$$
--
--   Since $(\bar d+1)^2\le4\log_2^2k$ for $k\ge2$, the ratio is $O(p\log^2k)$; it depends only on $k$ and the class. Planar graphs ($p=3$) and graphs of bounded treewidth are such classes.
--
--   **Formalization Note** The machine computes, on every such instance, the output of some run of LPSEP; its running-time exponent may depend on $p$, the class and $Z$, but not on the instance.
--
--   Differences from the source:
--   - reading: G a p-root-path separable class, LPSEP run with the separator algorithm of Definition 5.1 for G → hypotheses MinorClosed G, every connected graph of G p-root-path separable, and IsClassAlgorithm p G Z for the algorithm Z with which LPSEP is run; reason: Definition 5.1 is the conjunction of these; its existence clause is supplied by Z itself
--   - encoding: a class of graphs → a predicate on graphs with vertex set Fin N, closed under isomorphism (part of MinorClosed); reason: every finite graph is isomorphic to one on some Fin N
--   - encoding: 14 min{p, k}(d̄ + 1)² OPT, d̄ = ⌊log₂ k⌋ → 14 * min p k * (Nat.log 2 k + 1)^2 * |S′| in ℕ for every valid S′ informing all terminals; reason: Nat.log 2 k = ⌊log₂ k⌋; all quantities are natural numbers
--   - encoding: polynomial time (no machine model named) → Mathlib Turing.TM2ComputableInTime over Fin 4 with time at most (m + 2)^c on inputs of length m, inputs encInst, outputs encSched; reason: the encoding is of size polynomial in n (adjacency matrix), so the bounds agree
--   - encoding: LPSEP (Algorithms 4 and 5), with its free choices → the machine outputs a schedule S with LPSepRun p Z I S, every free choice open; reason: the source leaves instance orders, weights, BFS trees and ties open; every run is admitted
--   - encoding: OPT, the minimum number of rounds of a feasible schedule → comparison with every valid schedule that informs all terminals; reason: no minimum over a possibly empty set is taken; same instances and same bound
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 5.2, p.14 (PDF p.15); restated p.37 (PDF p.38); proof p.48 (PDF p.49); Definition 5.1, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_encInst
import Definitions.Def_DirTeleMC_Supplement_IsRootPathSeparable
import Definitions.Def_DirTeleMC_Supplement_IsClassAlgorithm
import Definitions.Def_DirTeleMC_Supplement_LPSepRun

namespace DirTeleMC.Supplement

open DirTeleMC OnlineCRS.Combine

/-- **Theorem 5.2** (LPSEP on root-path separable classes).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 5.2, p.14 (restated p.37, proved p.48): "Let p ≥ 1 be an integer and G a
p-root-path separable class. When run with the separator algorithm of Definition 5.1 for G, LPSEP is a deterministic
polynomial-time algorithm that, given a digraph whose underlying graph lies in G, a source s and a set K of k ≥ 2
terminals reachable from s, computes a DTM schedule of length at most 14 min{p, k}(d̄ + 1)² OPT, where
d̄ = ⌊log₂ k⌋."

Let `p ≥ 1` and let `G` be a `p`-root-path separable class: minor-closed, with every connected graph in it
`p`-root-path separable, and let `Z` be a separator algorithm for it (Definition 5.1). Then there are a constant `c`
and a function `alg`, computed by a Turing machine in time at most `(m + 2)^c` on inputs of length `m`, such that on
every well-formed DTM instance (`k = |K|`) whose underlying graph lies in `G`, the output of `alg` is a schedule `S`
returned by a run of LPSEP with `p` and `Z`, `S` is valid and informs all terminals, and
`|S| ≤ 14 · min{p, k} · (⌊log₂ k⌋ + 1)² · |S′|` for every valid schedule `S′` that informs all terminals.

**Formalization Note.** Machine model: Mathlib's `Turing.TM2ComputableInTime` over the published alphabet `Fin 4`,
inputs encoded by `encInst`, outputs by `encSched`; `c` may depend on `p`, `G` and `Z`, not on the instance. OPT is
written as "every valid schedule `S′` informing all terminals". The separator algorithm is the function `Z` of
`IsClassAlgorithm` (computed in polynomial time and correct on the connected graphs of `G`). -/
theorem theorem_5_2 (p : ℕ) (hp : 1 ≤ p) (G : GraphClass) (hG : MinorClosed G)
    (hsep : ∀ N (H : SimpleGraph (Fin N)), G N H → H.Connected → IsRootPathSeparable p H)
    (Z : SepInput → List ℕ) (hZ : IsClassAlgorithm p G Z) :
    ∃ c : ℕ, ∃ alg : Inst → List (List (ℕ × ℕ)),
      (∃ M : Turing.TM2ComputableInTime encInst encSched alg, ∀ m, M.time m ≤ (m + 2) ^ c) ∧
      ∀ I : Inst, I.WF → I.k = I.K.card → G I.n (underlying I.adj) →
        ∃ S : Schedule I.n, alg I = S.toNat ∧ LPSepRun p Z I S ∧ S.Valid I ∧ S.InformsK I ∧
          ∀ S' : Schedule I.n, S'.Valid I → S'.InformsK I →
            S.length ≤ 14 * min p I.k * (Nat.log 2 I.k + 1) ^ 2 * S'.length := by sorry

end DirTeleMC.Supplement
