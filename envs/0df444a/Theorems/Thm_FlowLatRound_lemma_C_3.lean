-- Prove2me | Theorems.Thm_FlowLatRound_lemma_C_3
-- name    : FlowLatRound.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:09.382442+00:00
-- url     : https://prove2.me/theorems/e72c9e85-9722-499d-b619-926b1bcf16c0
-- title:
--   Lemma C.3 — closest vectors in flow lattices in time polynomial in $m$ and the bit length of $y$, by a deterministic algorithm
-- statement:
--   Given a connected multigraph $G$ with an orientation and a rational $y\in H_G$, the decoder `flowCVP` returns $z\in\Lambda_G$ with
--   $$\|z-y\|\le\|z'-y\|\quad\text{for all }z'\in\Lambda_G,$$
--   at bit cost at most $c\,(1+m+\mathrm{bits}(y))^k$, with constants $c,k$ independent of $G$ and $y$. The output is a deterministic function of $(G,y)$.
--
--   Lemma 3.1 (p.6) is the summary of this lemma used in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: (expected) polynomial time in the model of Appendix B (exact rational arithmetic, rejection sampling, expectation over the random choices) → a bit-cost counter (each operation charged (ratBits a + ratBits b + 1)^2, coin reads and list/array steps 1), a fair-coin tape with fuel-indexed halting, non-halting runs charged ⊤, expectation as ∫⁻ over the tape; polynomial = ∃ c k, one pair for all inputs; reason: a faithful rendering of Appendix B; the programs are named so the claim is about them
--   - generalization: a closest vector can be computed in polynomial time → the named decoder flowCVP returns a closest vector within cost c·(1 + m + bits(y))^k; reason: a specific algorithm with these properties implies the existence claim
--   - reading: "a polynomial-time minimum-cost flow algorithm" (unnamed) → successive shortest paths with Bellman–Ford after saturating all negative-cost unit arcs; reason: the decoder must be a defined program; any correct polynomial algorithm is acceptable, this one is fixed
--   - encoding: polynomial in m and the bit length of y → c·(1 + m + Σ_e ratBits y_e)^k; reason: the 1 + keeps the bound meaningful for m = 0
--   - encoding: G connected → 0 < τ(G); reason: a multigraph is connected iff it has a spanning tree
--   - encoding: H_G = ker A_G with one vertex row of the incidence matrix deleted → kernel of the full n×m incidence map; reason: the rows of the full matrix sum to zero, so both kernels are equal
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.3, p.23 (PDF 25); proof pp.23–24; Lemma 3.1, p.6 (PDF 8)

import Mathlib
import Definitions.Def_FlowLatRound_FlowCVP

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma C.3, p.23 (PDF 25) (summarized as Lemma 3.1, p.6). Closest vectors in flow
lattices: given a connected multigraph `G` with an orientation and a rational `y ∈ H_G`, the
decoder `flowCVP G y` returns a closest vector `z ∈ Λ_G` to `y`, at bit cost at most
`c (1 + m + bits(y))^k`, with one `(c, k)` for all inputs. The output is a deterministic function
of `(G, y)` (`flowCVP` is a function).

**Formalization Note.** "Time polynomial in `m` and the bit length of `y`" is the bit-cost
counter of the program bounded by `c·(1 + m + Σ_e ratBits y_e)^k`; the `1 +` makes the bound
meaningful for `m = 0`. -/
theorem lemma_C_3 :
    ∃ c k : ℕ, ∀ (n m : ℕ) (G : MGraph n m), 0 < G.tau → ∀ y : Fin m → ℚ,
      ratVec y ∈ G.flowSpace →
        intVec ((G.flowCVP y).run 0).1 ∈ G.flowLattice ∧
        (∀ z ∈ G.flowLattice, ‖intVec ((G.flowCVP y).run 0).1 - ratVec y‖ ≤ ‖z - ratVec y‖) ∧
        ((G.flowCVP y).run 0).2 ≤ c * (1 + m + bitsQ y) ^ k := by sorry

end FlowLatRound
