-- Prove2me | Theorems.Thm_ChanTomoNB_corollary_A_2
-- name    : ChanTomoNB.corollary_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:19.822929+00:00
-- url     : https://prove2.me/theorems/6e12c71c-c0a9-454a-817b-6fd4fbe5392d
-- title:
--   Corollary A.2 — $n\ge10^{-28}d_1^2/\varepsilon$ for $d_1\le rd_2\le4d_1/3$, $0<\varepsilon\le10^{-12}$
-- statement:
--   Let $d_1,d_2\ge2$, $r\ge1$ and $d_1\le rd_2\le4d_1/3$, and let $0<\varepsilon\le10^{-12}$. Tomography of $\mathbf{QChan}^r_{d_1,d_2}$ to Choi trace norm error $\varepsilon$, or to diamond norm error $\varepsilon$, with success probability at least $2/3$, requires
--   $$
--   n\ge10^{-28}\frac{d_1^2}{\varepsilon}.
--   $$
--
--   This Heisenberg term is the first summand of the Choi trace norm bound of Theorem 6.1.
--
--   Differences from the source:
--   - reading: an algorithm with query access that may use a reference system, quantum memory and adaptive inputs (pp.10, 12) → every tester with n queries (Definition 2.3): PSD operators T_i whose sum is a quantum (n+1)-comb; reason: the paper proves its lower bounds in the tester model and states that every sequential, adaptive, coherent algorithm is a tester (p.12); quantifying over all testers is the stronger reading
--   - generalization: a tester {T_i}_i → an arbitrary outcome type ι with ∑_i T_i converging entrywise (HasSum); reason: every finite tester is the case of a finite ι
--   - generalization: the estimate Ê (a channel) → estimates are arbitrary linear maps L(C^{d1}) → L(C^{d2}); reason: channels are a special case; both distances are defined by the p.10 formulas for every linear map
--   - encoding: ‖E − F‖_⋄ = max over density operators ρ_AR, H_R ≅ C^{d1} (p.10) → sSup of the same set of values ‖((E − F) ⊗ I_R)(ρ)‖_1, H_R ≅ C^{d1}; reason: the set is nonempty and bounded, so the supremum is the printed maximum
--   - encoding: QChan^r_{d1,d2}: channels of Kraus rank at most r (p.10) → maps X ↦ ∑_{i<r} K_i X K_i† with ∑_i K_i†K_i = I, zero Kraus operators allowed; reason: the same set: the Kraus rank is the rank of the Choi operator (p.10)
--   - encoding: C_E^{⊗n} on ⊗_j(H_{B,j} ⊗ H_{A,j}) and p_i = tr(T_i^T C_E^{⊗n}) (p.12) → a query is indexed Fin d1 × Fin d2 (input first), C_E^{⊗n} is reindexed to that order, and tr(T^T C) is the entrywise pairing ∑_{x,y} T_{xy} C_{xy}; reason: the same numbers
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Corollary A.2, p.40

import Mathlib
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist

open Matrix

namespace ChanTomoNB

/-- **Corollary A.2 (Heisenberg lower bound in all dimensions).** Chen, Oufkir, *Quantum channel
tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1, Corollary A.2, p.40:
"Let d1, d2 ≥ 2, r ≥ 1, and d1 ≤ rd2 ≤ 4d1/3. For 0 < ε ≤ 10^{−12}, tomography of QChan^r_{d1,d2}
to Choi trace norm or diamond norm error ε, with success probability at least 2/3, requires
n ≥ 10^{−28} d1²/ε."

**Formalization Note.** An algorithm is a tester (Reading 1) with arbitrary outcome type
(Reading 2) and estimates in all linear maps (Reading 3). "Choi trace norm or diamond norm" is
the conjunction of the two implications. `rd2 ≤ 4d1/3` is stated in `ℝ`. -/
theorem corollary_A_2 (d1 d2 r : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2) (hr : 1 ≤ r)
    (hlo : d1 ≤ r * d2) (hhi : (r : ℝ) * d2 ≤ 4 * (d1 : ℝ) / 3)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10 ^ 12) (n : ℕ) (T : Tester (Fin d1) (Fin d2) n)
    (est : T.ι → Superop (Fin d1) (Fin d2)) :
    (T.Learns est choiDist r ε → 1 / 10 ^ 28 * ((d1 : ℝ) ^ 2 / ε) ≤ (n : ℝ)) ∧
      (T.Learns est diamondDist r ε → 1 / 10 ^ 28 * ((d1 : ℝ) ^ 2 / ε) ≤ (n : ℝ)) := by sorry

end ChanTomoNB
