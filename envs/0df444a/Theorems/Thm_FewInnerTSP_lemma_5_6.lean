-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_5_6
-- name    : FewInnerTSP.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:52.331076+00:00
-- url     : https://prove2.me/theorems/498cc997-91d0-486a-9adc-fd23fe6dd13b
-- title:
--   Lemma 5.6 (Kernel running time)
-- statement:
--   There are a constant $C>0$ and one admissible real-RAM program, fixed before the input, such that for every set $P$ of $n\ge3$ points in general position with $k\ge1$ interior points and every counterclockwise hull order, on the reduced mixed instance of §3 — the interior points, the retained skeleton vertices in cyclic order, and each skeleton edge's mandatory flag and stored chain weight — the program halts within
--   $$2^{C(\sqrt k+\log^3(k+2))}$$
--   steps and outputs a minimum mixed Hamiltonian cycle, by the identities of its edges.
--
--   With Lemma 3.3 this solves the original instance up to expanding the stored chains, which gives Theorem 1.1.
--
--   **Formalization Note** The output is the number of edges, then the code of each edge relative to the vertex list (interior points, then skeleton vertices).
--
--   Differences from the source:
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - reading: solved … including representative construction and traceback information → the program outputs a minimum mixed Hamiltonian cycle itself, by edge identities; reason: 'traceback' means the cycle comes out, not only its weight
--   - encoding: 2^{O(√k + log³(k+2))} arithmetic operations → (T+1) ≤ 2^{C(√k + log³(k+2))} with C fixed before the input; reason: O-notation with the constant before the input
--   - reading: the reduced mixed instance of §3, defined after 'The case k = 0 is solved directly' → k ≥ 1, the instance being reducedSkeleton of a general-position P with a counterclockwise hull order, given by the kernel layout; reason: the reduction is defined only for k > 0
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.6, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FewInnerTSP_MixedInstance
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

/-- **Lemma 5.6 (Kernel running time).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.6, p.12 (PDF p.14):
"The reduced mixed instance can be solved in 2^{O(√k+log³(k+2))} arithmetic operations, including
representative construction and traceback information."

There are `C > 0` and one admissible program, fixed before the input, such that for every `n ≥ 3`
general-position points with `k ≥ 1` interior points and a counterclockwise hull order, on the reduced
mixed instance of §3 (`Γ = reducedSkeleton P hull`) given as `kernelLayout` (`k`, `m = |H₀|`, the interior
points in any order, the retained vertices in cyclic order, and for each skeleton edge its mandatory flag
and stored weight), the run halts within `2^{C(√k + log³(k+2))}` steps and outputs the edge codes of a
minimum mixed Hamiltonian cycle.

**Formalization Note** "Solved … including traceback information" is read as outputting a minimum cycle
itself, by its edge identities, not only its weight. The output is the number of edges followed by three
cells per edge code, relative to the vertex list `I ++ H₀`. -/
theorem lemma_5_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ Prog : MatMulTimeLP.Program, Admissible Prog ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ P : Fin n → Pt, GeneralPos P → ∀ (h : ℕ) (hull : Fin h → Fin n),
      IsHullOrder P hull → 0 < interiorCount P → ∀ I : List (Fin n), IsListing I (interiorIdx P) →
      ∀ ω : MatMulTimeLP.Tape, ∃ (T : ℕ) (L : List EdgeCode)
        (Tc : Finset (Edge n (retainedPos P hull).card)),
        MatMulTimeLP.HaltsAt Prog (kernelLayout P (reducedSkeleton P hull) I) ω T ∧
        (T : ℝ) + 1 ≤ (2 : ℝ) ^ (C * (Real.sqrt (interiorCount P : ℝ) +
          Real.log ((interiorCount P : ℝ) + 2) ^ 3)) ∧
        OutputIs Prog (kernelLayout P (reducedSkeleton P hull) I) ω T
          ((L.length : ℝ) :: encodeEdges L) ∧
        DecodesTo (I ++ List.ofFn (reducedSkeleton P hull).vert) L Tc ∧
        IsMinMixedCycle P (reducedSkeleton P hull) Tc := by sorry

end FewInnerTSP
