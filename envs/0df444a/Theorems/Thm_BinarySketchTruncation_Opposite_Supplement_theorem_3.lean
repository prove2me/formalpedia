-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_theorem_3
-- name    : BinarySketchTruncation.Opposite.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:59.109723+00:00
-- url     : https://prove2.me/theorems/82f55efd-ae77-4b5d-bcce-7bc89412cd4e
-- title:
--   Theorem 3 — nonlinear messages versus linear sketches for connectivity
-- statement:
--   For each integer v, let G(Z) be the uniform random spanning subgraph of K_{v,2^v}, with n=v+2^v vertices and m=v·2^v possible edges. There is a threshold v₀ such that, for every v ≥ v₀, both statements hold:
--
--   1. There are a deterministic encoder φ with a (3v+3)-bit message and a deterministic decoder g such that, for every simple graph H on the same vertex set,
--
--   $$
--   \widetilde e_H(\varphi,g)\le\frac1{10}.
--   $$
--
--   2. For every k, every k-row binary matrix A and every deterministic decoder g, if the same decoder has error at most 1/10 for every H, then
--
--   $$
--   m\le2k \quad\text{or equivalently}\quad k\ge m/2.
--   $$
--
--   Here the error is over Z alone and tests connectivity of G(Z) ∪ H. The encoder and decoder are chosen before H, which ranges over all simple graphs, including non-bipartite graphs. This gives the paper's separation between deterministic nonlinear messages and binary linear sketches, with its exact bit and error bounds. The source's O(log n) and Ω(n log n) annotations describe the displayed bounds after substituting n=v+2^v; the formal statement retains the exact 3v+3 and m/2 claims.
--
--   Differences from the source:
--   - reading: a deterministic protocol using 3v+3 bits (Appendix A.1 sends either a single failure bit or a leading 0, a two-bit count and up to three v-bit labels) → a deterministic map into exactly 3v+3 binary coordinates; reason: of the readings "at most 3v+3 bits, variable length" and "exactly 3v+3 bits", the fixed-length one is the stronger and implies the other; the source protocol fits it by padding with zeroes, since the leading flag and the count field make every padded message decodable
--   - generalization: a k-bit binary linear sketch AZ with A of rank k → every k-row binary matrix A, of any rank; reason: restricted to rank-k matrices it is the source's claim; for a matrix of rank r < k the same claim follows from the source's bound r ≥ m/2 applied to an equivalent full-row-rank r-row sketch
--   - encoding: for all sufficiently large v, with bounds 3v+3 = O(log n) and k ≥ m/2 = Ω(n log n) → one natural threshold v₀ for both clauses, exact message length 3v+3, error 1/10 and natural inequality v·2^v ≤ 2k; reason: this is the quantified meaning of sufficiently large; the O and Ω annotations follow from n=v+2^v and do not change the exact bounds
--   - encoding: graphs on a common vertex set and a uniform m-edge indicator vector → Mathlib SimpleGraphs on Fin v ⊕ Fin (2^v), and ZMod 2 vectors indexed by the bipartite edge pairs; reason: the sum type keeps every vertex, graph supremum is union, and uniform probability is over Z alone for each fixed arbitrary H
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 11–12 (PDF pp. 12–13), Theorem 3; pp. 18–20 (PDF pp. 19–21), Appendices A.1–A.3

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_Connectivity

namespace BinarySketchTruncation.Opposite.Supplement

/-- Theorem 3, printed pp. 11–12 (PDF 12–13). One threshold for both clauses;
H is arbitrary, while the encoder and the decoder are fixed before H.
The 3v+3-bit message is obtained by padding the source's shorter messages. -/
theorem theorem_3 :
    ∃ v₀ : ℕ, ∀ v : ℕ, v₀ ≤ v →
      (∃ (φ : ((Fin v × Fin (2 ^ v)) → Bit) → Vec (3 * v + 3))
          (g : Vec (3 * v + 3) → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool),
        ∀ H : SimpleGraph (Fin v ⊕ Fin (2 ^ v)),
          connectivityError φ g H ≤ (1 / 10 : ℝ)) ∧
      (∀ (k : ℕ) (A : Matrix (Fin k) (Fin v × Fin (2 ^ v)) Bit)
          (g : Vec k → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool),
        (∀ H : SimpleGraph (Fin v ⊕ Fin (2 ^ v)),
          connectivityError (fun z => A.mulVec z) g H ≤ (1 / 10 : ℝ)) →
        v * 2 ^ v ≤ 2 * k) := by sorry

end BinarySketchTruncation.Opposite.Supplement
