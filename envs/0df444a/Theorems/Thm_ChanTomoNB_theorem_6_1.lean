-- Prove2me | Theorems.Thm_ChanTomoNB_theorem_6_1
-- name    : ChanTomoNB.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:43.992496+00:00
-- url     : https://prove2.me/theorems/3aa74308-175b-4af8-ad57-66523cb33503
-- title:
--   Theorem 6.1 — near-boundary bounds: $n\ge rd_1d_2/(3072e^3\varepsilon^2)$ (diamond), $n\ge(d_1^2/\varepsilon+\min\{(\tau-1)d_1^2,(\tau-1)^2d_1^2d_2^2\}/\varepsilon^2)/(2\cdot10^{28})$ (Choi)
-- statement:
--   Let $d_1,d_2\ge2$ and $r\ge1$ be integers with $d_1<rd_2<\frac43d_1$, and write $\tau=rd_2/d_1$. Consider any algorithm that, given query access to an unknown $\mathcal E\in\mathbf{QChan}^r_{d_1,d_2}$, makes $n$ queries (sequential, adaptive and coherent, with a reference system and quantum memory) and outputs an estimate $\hat{\mathcal E}$.
--
--   1. Let $0<\varepsilon\le1/(8e^{3/2}\sqrt8)$. If $\|\hat{\mathcal E}-\mathcal E\|_\diamond\le\varepsilon$ with probability at least $2/3$ for every $\mathcal E$, then
--   $$
--   n\ge\frac1{3072e^3}\cdot\frac{rd_1d_2}{\varepsilon^2}.
--   $$
--   2. Let $0<\varepsilon\le10^{-12}$. If $\frac1{d_1}\|C_{\hat{\mathcal E}}-C_{\mathcal E}\|_1\le\varepsilon$ with probability at least $2/3$ for every $\mathcal E$, then
--   $$
--   n\ge\frac1{2\cdot10^{28}}\Big(\frac{d_1^2}{\varepsilon}+\frac{\min\{(\tau-1)d_1^2,(\tau-1)^2d_1^2d_2^2\}}{\varepsilon^2}\Big).
--   $$
--
--   Under the diamond norm, classical $1/\varepsilon^2$ scaling appears as soon as $\tau>1$; under the Choi trace norm, the classical term grows gradually with $\tau-1$. Together with the matching upper bounds these settle the query complexity of channel tomography near the boundary $\tau=1$.
--
--   **Formalization Note** The algorithm is a tester (Definition 2.3); the probability of success is the total probability of the outcomes whose estimate is within $\varepsilon$ of $\mathcal E$. The hypotheses $d_1<rd_2<\frac43d_1$ are stated over the reals. The quantity $\chi=\min\{\alpha d_1,\alpha^2d_2^2\}$ of the printed hypothesis line is notation only.
--
--   Differences from the source:
--   - reading: an algorithm with query access that may use a reference system, quantum memory and adaptive inputs (pp.10, 12) → every tester with n queries (Definition 2.3): PSD operators T_i whose sum is a quantum (n+1)-comb; reason: the paper proves its lower bounds in the tester model and states that every sequential, adaptive, coherent algorithm is a tester (p.12); quantifying over all testers is the stronger reading
--   - generalization: a tester {T_i}_i → an arbitrary outcome type ι with ∑_i T_i converging entrywise (HasSum); reason: every finite tester is the case of a finite ι
--   - generalization: the estimate Ê (a channel) → estimates are arbitrary linear maps L(C^{d1}) → L(C^{d2}); reason: channels are a special case; both distances are defined by the p.10 formulas for every linear map
--   - encoding: ‖E − F‖_⋄ = max over density operators ρ_AR, H_R ≅ C^{d1} (p.10) → sSup of the same set of values ‖((E − F) ⊗ I_R)(ρ)‖_1, H_R ≅ C^{d1}; reason: the set is nonempty and bounded, so the supremum is the printed maximum
--   - encoding: QChan^r_{d1,d2}: channels of Kraus rank at most r (p.10) → maps X ↦ ∑_{i<r} K_i X K_i† with ∑_i K_i†K_i = I, zero Kraus operators allowed; reason: the same set: the Kraus rank is the rank of the Choi operator (p.10)
--   - encoding: C_E^{⊗n} on ⊗_j(H_{B,j} ⊗ H_{A,j}) and p_i = tr(T_i^T C_E^{⊗n}) (p.12) → a query is indexed Fin d1 × Fin d2 (input first), C_E^{⊗n} is reindexed to that order, and tr(T^T C) is the entrywise pairing ∑_{x,y} T_{xy} C_{xy}; reason: the same numbers
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Theorem 6.1, p.33

import Mathlib
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist

open Matrix

namespace ChanTomoNB

/-- **Theorem 6.1 (Near-boundary query lower bounds).** Chen, Oufkir, *Quantum channel
tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1, Theorem 6.1, p.33:
"Let d1, d2 ≥ 2 and r ≥ 1 be integers satisfying d1 < rd2 < (4/3)d1. Write τ = rd2/d1,
α = rd2 − d1, and χ = min{αd1, α²d2²}. Suppose an algorithm, given query access to any unknown
E ∈ QChan^r_{d1,d2}, makes n queries and outputs an estimate Ê.
• Assume 0 < ε ≤ 1/(8e^{3/2}√8). If ‖Ê − E‖_⋄ ≤ ε with probability at least 2/3, then
  n ≥ (1/(3072e³)) · rd1d2/ε².
• Assume 0 < ε ≤ 10^{−12}. If (1/d1)‖C_Ê − C_E‖_1 ≤ ε with probability at least 2/3, then
  n ≥ (1/(2 · 10^{28})) · (d1²/ε + min{(τ − 1)d1², (τ − 1)²d1²d2²}/ε²)."

For every `n`, every `n`-query tester (sequential, adaptive, coherent; Definition 2.3) and every
estimate map on its outcomes, both bullets hold.

**Formalization Note.** Reading 1: an algorithm is a tester (the model in which the paper proves
its lower bounds, pp.10, 12). Reading 2: the outcome type is arbitrary and `∑ᵢ Tᵢ` converges
(`HasSum`). Reading 3: estimates range over all linear maps `L(ℂ^{d1}) → L(ℂ^{d2})`. Reading 4:
`‖·‖_⋄` has the reference `H_R ≅ ℂ^{d1}` and the maximum over density operators (p.10). Reading 5:
`QChan^r` uses Kraus families of length `r`, zeros allowed. Reading 6: a query is indexed
`Fin d1 × Fin d2` and `tr(Tᵀ C_E^{⊗n})` is the entrywise pairing. `Learns` requires success with
probability `≥ 2/3` for every `E ∈ QChan^r`. The inequalities `d1 < r d2 < (4/3) d1` are stated in
`ℝ`; `χ` is notation of the hypothesis line and is not used in the conclusions. -/
theorem theorem_6_1 (d1 d2 r : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2) (hr : 1 ≤ r)
    (hlo : (d1 : ℝ) < (r : ℝ) * d2) (hhi : (r : ℝ) * d2 < 4 / 3 * (d1 : ℝ))
    (n : ℕ) (T : Tester (Fin d1) (Fin d2) n) (est : T.ι → Superop (Fin d1) (Fin d2)) (ε : ℝ) :
    (0 < ε → ε ≤ 1 / (8 * Real.exp (3 / 2) * Real.sqrt 8) → T.Learns est diamondDist r ε →
        1 / (3072 * Real.exp 3) * ((r : ℝ) * d1 * d2 / ε ^ 2) ≤ (n : ℝ)) ∧
      (0 < ε → ε ≤ 1 / 10 ^ 12 → T.Learns est choiDist r ε →
        1 / (2 * 10 ^ 28) * ((d1 : ℝ) ^ 2 / ε +
          min (((r : ℝ) * d2 / d1 - 1) * (d1 : ℝ) ^ 2)
            (((r : ℝ) * d2 / d1 - 1) ^ 2 * (d1 : ℝ) ^ 2 * (d2 : ℝ) ^ 2) / ε ^ 2) ≤ (n : ℝ)) := by sorry

end ChanTomoNB
