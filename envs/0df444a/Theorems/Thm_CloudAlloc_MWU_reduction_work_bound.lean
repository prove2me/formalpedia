-- Prove2me | Theorems.Thm_CloudAlloc_MWU_reduction_work_bound
-- name    : CloudAlloc.MWU.reduction_work_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:10.816415+00:00
-- url     : https://prove2.me/theorems/17fb5567-33b7-47f0-9e69-6337c4cbf34a
-- title:
--   Proof of Theorem 1: the reduction display $\mathrm{work}_{\mathrm{alg}}\ge(1-4\varepsilon)\mathrm{work}_h-2000\frac{N}{\varepsilon^2\eta}\ln(N/\varepsilon)$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta\ge 0$ with $\sum_i\beta(i)\le 1$, nonnegative loads, and $h^{\mathrm{alg}}$ a run of Algorithm 1. For every horizon $T$ and every offline allocation sequence $h_1,\dots,h_T$ ($h_t\ge 0$, $\sum_i h_t(i)\le 1$), with $\bar h_t=(1-4\varepsilon)h_t$:
--
--   1. $\displaystyle \mathrm{work}_{\mathrm{alg}}\ \ge\ \mathrm{work}_{\bar h_1,\dots,\bar h_T}-8\,\frac{N}{(\varepsilon/4)^2\eta}\ln(4N/\varepsilon)$;
--   2. $\displaystyle \mathrm{work}_{\mathrm{alg}}\ \ge\ (1-4\varepsilon)\,\mathrm{work}_{h_1,\dots,h_T}-2000\,\frac{N}{\varepsilon^2\eta}\ln(N/\varepsilon)$.
--
--   Both inequalities of the display on p. 10 are stated as printed, with the algorithm run at $\varepsilon$. This is the paper's route from Theorem 3 to the work guarantee of Theorem 1.
--
--   Differences from the source:
--   - generalization: offline policy with Σ_i h_t(i) = 1 → every nonnegative sequence with Σ_i h_t(i) ≤ 1; reason: contains the printed policies
--   - generalization: η in Algorithm 1's input range 0 < η < 1/3 (no η range printed in this statement) → 0 < η ≤ 1/3; reason: the range printed in Lemma 2 and Theorem 4; it contains Algorithm 1's input range, so the statement specializes to it
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §3, p. 10 (unnumbered display after Theorem 3)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_totalWork

namespace CloudAlloc.MWU

/-- **The reduction display: work against full allocations (derivation of Theorem 1, p. 10).**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, §3, p. 10 (unnumbered display):
"Given any offline dynamic policy `h1, . . . , hT` such that `Σ_i ht(i) = 1`, we define
`h̄t := (1 − 4ε)ht`, which satisfies the assumption of Theorem 3. Now we have
`work_alg ≥ work_{h̄1,...,h̄T} − 8 N/((ε/4)²η) ln(4N/ε) ≥ (1 − 4ε) · work_{h1,...,hT} − 2000 N/(ε²η) ln(N/ε)`".

For a run of Algorithm 1 (standing hypotheses, `0 < η ≤ 1/3`), every horizon `T` and every offline
allocation sequence `h` (nonnegative, summing to at most `1` at each step):
(1) `work_alg ≥ work_{(1−4ε)h} − 8N/((ε/4)²η)·ln(4N/ε)`, and
(2) `work_alg ≥ (1 − 4ε)·work_h − 2000N/(ε²η)·ln(N/ε)`.

**Formalization Note.** Lean time `t` is the paper's `t + 1`; each allocation sequence has its own
queues on the same loads, from `Q_1 = 0`. Both inequalities of the display are stated as printed,
with Algorithm 1 run at `ε`. The benchmark is any sequence with `Σ_i h_t(i) ≤ 1` (printed `= 1`), which
includes the printed ones. The η range `0 < η ≤ 1/3` is that of corrected Theorem 3. -/
theorem reduction_work_bound {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    ∀ (T : ℕ) (hs : ℕ → Fin N → ℝ), (∀ t < T, (∀ i, 0 ≤ hs t i) ∧ ∑ i, hs t i ≤ 1) →
      totalWork (fun t j => (1 - 4 * ε) * hs t j) L T
          - 8 * (N : ℝ) / ((ε / 4) ^ 2 * η) * Real.log (4 * (N : ℝ) / ε) ≤ totalWork h L T ∧
        (1 - 4 * ε) * totalWork hs L T
          - 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) ≤ totalWork h L T := by sorry

end CloudAlloc.MWU
