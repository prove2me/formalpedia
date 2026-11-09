-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_A_1
-- name    : ChanTomoNB.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:25.064204+00:00
-- url     : https://prove2.me/theorems/85b7aeb1-aa5d-4646-80f3-2e158e154b42
-- title:
--   Lemma A.1 — $n\ge1/(9\varepsilon)$ for Choi trace norm and diamond norm tomography, $rd_2\ge d_1$
-- statement:
--   Let $d_1,d_2\ge2$ and $r\ge1$ with $rd_2\ge d_1$, and let $0<\varepsilon\le1/6$. If an $n$-query algorithm (with arbitrary estimates) learns every channel in $\mathbf{QChan}^r_{d_1,d_2}$ to Choi trace norm error $\varepsilon$ with success probability at least $2/3$, then
--   $$
--   n\ge\frac1{9\varepsilon}.
--   $$
--   The same bound holds for diamond norm error.
--
--   This is the Heisenberg-scaling lower bound in all dimensions, used for small dimensions in Corollary A.2.
--
--   Differences from the source:
--   - reading: an algorithm with query access that may use a reference system, quantum memory and adaptive inputs (pp.10, 12) → every tester with n queries (Definition 2.3): PSD operators T_i whose sum is a quantum (n+1)-comb; reason: the paper proves its lower bounds in the tester model and states that every sequential, adaptive, coherent algorithm is a tester (p.12); quantifying over all testers is the stronger reading
--   - generalization: a tester {T_i}_i → an arbitrary outcome type ι with ∑_i T_i converging entrywise (HasSum); reason: every finite tester is the case of a finite ι
--   - generalization: the estimate Ê (a channel) → estimates are arbitrary linear maps L(C^{d1}) → L(C^{d2}); reason: channels are a special case; both distances are defined by the p.10 formulas for every linear map
--   - encoding: ‖E − F‖_⋄ = max over density operators ρ_AR, H_R ≅ C^{d1} (p.10) → sSup of the same set of values ‖((E − F) ⊗ I_R)(ρ)‖_1, H_R ≅ C^{d1}; reason: the set is nonempty and bounded, so the supremum is the printed maximum
--   - encoding: QChan^r_{d1,d2}: channels of Kraus rank at most r (p.10) → maps X ↦ ∑_{i<r} K_i X K_i† with ∑_i K_i†K_i = I, zero Kraus operators allowed; reason: the same set: the Kraus rank is the rank of the Choi operator (p.10)
--   - encoding: C_E^{⊗n} on ⊗_j(H_{B,j} ⊗ H_{A,j}) and p_i = tr(T_i^T C_E^{⊗n}) (p.12) → a query is indexed Fin d1 × Fin d2 (input first), C_E^{⊗n} is reindexed to that order, and tr(T^T C) is the entrywise pairing ∑_{x,y} T_{xy} C_{xy}; reason: the same numbers
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma A.1, p.38

import Mathlib
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist

open Matrix

namespace ChanTomoNB

/-- **Lemma A.1.** Chen, Oufkir, *Quantum channel tomography: optimal bounds in the near-boundary
regime*, arXiv:2611.03639v1, Lemma A.1, p.38: "Let d1, d2 ≥ 2 and r ≥ 1 satisfy rd2 ≥ d1. If an
algorithm uses n queries to learn every channel in QChan^r_{d1,d2} to Choi trace norm error
0 < ε ≤ 1/6, with success probability at least 2/3, then n ≥ 1/(9ε). The same bound holds for
diamond norm error."

For every `n`-query tester and estimate map: if it learns every `E ∈ QChan^r_{d1,d2}` to Choi
trace norm distance `ε` with probability at least `2/3`, then `n ≥ 1/(9ε)`; the same holds for the
diamond norm distance.

**Formalization Note.** An algorithm is a tester (Definition 2.3, Reading 1) with arbitrary
outcome type (Reading 2) and estimates in all linear maps (Reading 3); `Learns` requires success
for every `E ∈ QChan^r`. Both metrics are as on p.10 (reference `H_R ≅ ℂ^{d1}` for the diamond
norm). -/
theorem lemma_A_1 (d1 d2 r : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (h : d1 ≤ r * d2)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 6) (n : ℕ) (T : Tester (Fin d1) (Fin d2) n)
    (est : T.ι → Superop (Fin d1) (Fin d2)) :
    (T.Learns est choiDist r ε → 1 / (9 * ε) ≤ (n : ℝ)) ∧
      (T.Learns est diamondDist r ε → 1 / (9 * ε) ≤ (n : ℝ)) := by sorry

end ChanTomoNB
