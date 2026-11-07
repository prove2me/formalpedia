-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_3_3
-- name    : DisjointPathsDAG.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:11.084347+00:00
-- url     : https://prove2.me/theorems/fba345ed-61d2-4b45-a902-2042c6f14278
-- title:
--   Lemma 3.3 (Interpolated coefficient extraction)
-- statement:
--   There are constants $C$, $A$ and one machine program such that the following holds over every finite field $F$. Let $Q$ be a nonzero homogeneous multilinear polynomial of degree $j$ with $|F|\ge2j$, computed (as a formal polynomial) by a division-free program $P$ of size $S$, counting gates and input occurrences, with constants given in field cells. Run on $(j,P)$:
--
--   1. the expected running time is at most $C\,(j^2+1)\,S$;
--   2. every run uses at most $C\,S$ cells;
--   3. every halting run outputs a set $B$ of $j$ distinct variables together with $c_B$, where $c_B$ is the coefficient of $z^B$ in $Q$ and $c_B\neq0$.
--
--   The extraction step of the reporting algorithm uses this to find a nonzero monomial without expanding $Q$.
--
--   **Formalization Note** Every machine instruction counts as one operation, so the bound covers all bookkeeping, not only field operations.
--
--   Differences from the source:
--   - reading: $O((j^2+1)S)$ field operations → at most $C(j^2+1)S$ machine steps in expectation; reason: every instruction is counted, which is the stronger reading
--   - encoding: a circuit computing $Q$ → the words `j :: P.encode` and the constants in field cells; $Q$ = `P.formalOut` at output 0; reason: the machine of Section 2.1
--   - encoding: $O(S)$ space → `spaceUsed ≤ C * S`: cells whose content changes; reason: the input is not charged
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.3 (Interpolated coefficient extraction), p.9

import Mathlib
import Definitions.Def_DisjointPathsDAG_Machine

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.3 (Interpolated coefficient extraction),
p.9: "Let Q be a nonzero homogeneous multilinear polynomial of degree j over a field F with |F| ≥ 2j,
computed by a division-free circuit of size S, counting gates and input occurrences. A set B of j
variables whose monomial has a nonzero coefficient cB in Q can be found, together with cB, using
expected O((j2 + 1)S) field operations and O(S) space."

There are constants `C`, `A` and one machine program `Prog` such that, over every finite field `F`, for
every `j` and every program `P` of size `S` with constant table `cs` whose output `0` is a nonzero,
homogeneous, multilinear polynomial `Q` of degree `j`, with `2j ≤ |F|`: run on the input `(j, P)` (words
`j` and the encoding of `P`; field cells: the constants `cs`) with width `A · ⌈log₂(size + 2)⌉`,
1. the expected running time is at most `C · (j² + 1) · S` (and the running time is measurable);
2. every run uses at most `C · S` cells;
3. every halting run outputs `j` distinct variable indices `B` and the field element `c_B` (field output
   `0`), with `c_B` the coefficient of `z^B` in `Q` and `c_B ≠ 0`.

**Formalization Note** Every machine instruction counts as one operation, bookkeeping included, which
is at least the number of field operations. The variables of `P` are its input indices (natural numbers);
the constant gate `const d c` reads `cs[c]` (`0` beyond the list). Space counts the cells whose content
changes (`spaceUsed`), so the input itself is not charged. -/
theorem lemma_3_3 :
    ∃ (C : ℝ) (A : ℕ) (Prog : Program), 0 < C ∧ 1 ≤ A ∧
      ∀ (F : Type) [Field F] [Finite F] (j : ℕ) (P : SLP) (cs : List F),
        P.formalOut (fun c => cs.getD c 0) 0 ≠ 0 →
        (P.formalOut (fun c => cs.getD c 0) 0).IsHomogeneous j →
        (∀ d ∈ (P.formalOut (fun c => cs.getD c 0) 0).support, ∀ e, d e ≤ 1) →
        2 * j ≤ Nat.card F →
        Measurable (fun ω => (haltTime (wordWidth A (Input.size (⟨j :: P.encode, [], cs⟩ : Input F)))
          F Prog ⟨j :: P.encode, [], cs⟩ ω : ℝ≥0∞)) ∧
        ∫⁻ ω, (haltTime (wordWidth A (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog
            ⟨j :: P.encode, [], cs⟩ ω : ℝ≥0∞) ∂(tapeLaw F) ≤
          ENNReal.ofReal (C * ((j : ℝ) ^ 2 + 1) * P.size) ∧
        (∀ ω : Tape F, (spaceUsed (wordWidth A (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F
          Prog ⟨j :: P.encode, [], cs⟩ ω : ℝ≥0∞) ≤ ENNReal.ofReal (C * P.size)) ∧
        ∀ (ω : Tape F) (t : ℕ),
          HaltsAt (wordWidth A (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog
            ⟨j :: P.encode, [], cs⟩ ω t →
          (outWords (⟨j :: P.encode, [], cs⟩ : Input F) (stateAt (wordWidth A
              (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog ⟨j :: P.encode, [], cs⟩ ω t)).Nodup ∧
          (outWords (⟨j :: P.encode, [], cs⟩ : Input F) (stateAt (wordWidth A
              (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog ⟨j :: P.encode, [], cs⟩ ω t)).length = j ∧
          (P.formalOut (fun c => cs.getD c 0) 0).coeff
              (∑ e ∈ (outWords (⟨j :: P.encode, [], cs⟩ : Input F) (stateAt (wordWidth A
                (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog ⟨j :: P.encode, [], cs⟩ ω t)).toFinset,
                Finsupp.single e 1) =
            outField (⟨j :: P.encode, [], cs⟩ : Input F) (stateAt (wordWidth A
              (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog ⟨j :: P.encode, [], cs⟩ ω t) 0 ∧
          outField (⟨j :: P.encode, [], cs⟩ : Input F) (stateAt (wordWidth A
              (Input.size (⟨j :: P.encode, [], cs⟩ : Input F))) F Prog ⟨j :: P.encode, [], cs⟩ ω t) 0 ≠ 0 := by sorry

end DisjointPathsDAG
