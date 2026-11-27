-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_4_2_11
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_4_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:52:57.246948+00:00
-- url     : https://prove2.me/theorems/7c54e3c8-5090-446a-8293-76e8db15ac79
-- title:
--   Theorem 4.2.11 — HARA utility: closed-form value on E_n and affine optimal investment
-- statement:
--   Let $U(x) = (x + b)^\gamma $ be the HARA-utility with $b \ge  0$ and $0 < \gamma  < 1$, so $dom U = \{x | x + b \ge  0\}$; let $E_n := \{x \in  \mathbb R  | x S^0_N/S^0_n + b \ge  0\}$ and `D_n(x) := {a ∈ ℝ^d | (1 + i_{n+1})(x + a · R_{n+1}) ∈ E_{n+1} ℙ-a.s.}`, $x \in  E_n$. Then: a) the value functions are $V_n(x) = d_n (x S^0_N/S^0_n + b)^\gamma $, $x \in  E_n$, with $d_N = 1$ and $d_n = \prod _{k=n}^{N-1} v_k$, where $v_n$ is the value of problem (4.7); b) the optimal amounts invested in the stocks are $f^*_n(x) = \alpha ^*_n (x + b S^0_n/S^0_N)$, $x \in  E_n$, where $\alpha ^*_n$ is the optimal solution of problem (4.7); the optimal portfolio strategy is $(f^*_0, \dots , f^*_{N-1})$.
--
--   **Formalization Note.** Assumption (FM) of §4.2 is in force ("Throughout we suppose that Assumption (FM) is valid", p.83). The state sets are those of p.88, not $dom U$ at every stage. $v_k$ is `powerValue` in $[0, \infty ]$; part a) includes that each $v_k$ is finite, so `toReal` loses nothing. "The optimal solution" $\alpha ^*_n$ of (4.7) is any maximizer (it exists by Theorem 4.1.1, which is included); b) is stated for every choice. $b = 0$ is allowed. Optimality means $V_{0\pi }(x) = V_0(x)$ for $x \in  E_0$.
--
--   Differences from the source:
--   - reading: α*_n the optimal solution of (4.7) → existence of a maximizer included; b) for every maximizer; reason: the problem may have several maximizers; every one gives the stated optimal strategy
--   - encoding: v_n the value of (4.7) → powerValue in [0,∞], shown finite; reason: Lean convention; same values
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.2.11, p.88 (PDF 102)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_NoArbitrage_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_PartialObs_S0
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_FM
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_wealth
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_D
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_Vpi
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_bellmanQ
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsMaximizer
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_powerValue

open MeasureTheory
open BauerleRiederMDP.PartialObs (S0)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 4.2.11** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 4.2.11, p.88, PDF 102, with the model of p.88). Let `U(x) = (x + b)^γ` be the
HARA-utility with `b ≥ 0` and `0 < γ < 1`, so `dom U = {x | x + b ≥ 0}`; let
`E_n := {x ∈ ℝ | x S^0_N/S^0_n + b ≥ 0}` and
`D_n(x) := {a ∈ ℝ^d | (1 + i_{n+1})(x + a · R_{n+1}) ∈ E_{n+1} ℙ-a.s.}`, `x ∈ E_n`. Then:
a) the value functions are `V_n(x) = d_n (x S^0_N/S^0_n + b)^γ`, `x ∈ E_n`, with `d_N = 1` and
`d_n = ∏_{k=n}^{N−1} v_k`, where `v_n` is the value of problem (4.7);
b) the optimal amounts invested in the stocks are `f*_n(x) = α*_n (x + b S^0_n/S^0_N)`, `x ∈ E_n`,
where `α*_n` is the optimal solution of problem (4.7); the optimal portfolio strategy is
`(f*_0, …, f*_{N−1})`.

**Formalization Note.** Assumption (FM) of §4.2 is in force ("Throughout we suppose that Assumption
(FM) is valid", p.83). The state sets are those of p.88, not `dom U` at every stage. `v_k` is
`powerValue` in `[0, ∞]`; part a) includes that each `v_k` is finite, so `toReal` loses nothing.
"The optimal solution" `α*_n` of (4.7) is any maximizer (it exists by Theorem 4.1.1, which is
included); b) is stated for every choice. `b = 0` is allowed. Optimality means
`V_{0π}(x) = V_0(x)` for `x ∈ E_0`. -/
theorem theorem_4_2_11 {d N : ℕ} (Mk : TWMarket d) (hFM : Mk.FM N) (b γ : ℝ) (hb : 0 ≤ b)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let U : ℝ → ℝ := fun x => (x + b) ^ γ
    let Es : ℕ → Set ℝ := fun n => {x | x * (S0 Mk.i N / S0 Mk.i n) + b ≥ 0}
    let A : ℕ → Set (Fin d → ℝ) := fun n =>
      {α | ∀ᵐ z ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ)), 0 ≤ 1 + α ⬝ᵥ z}
    (∀ k < N, Mk.powerValue γ k ≠ ⊤) ∧
    (∀ n ≤ N, ∀ x ∈ Es n, Mk.V Es U N n x =
      (((∏ k ∈ Finset.Ico n N, (Mk.powerValue γ k).toReal) *
        (x * (S0 Mk.i N / S0 Mk.i n) + b) ^ γ : ℝ) : EReal)) ∧
    (∀ n < N, ∃ α ∈ A n, ∫⁻ z, ENNReal.ofReal ((1 + α ⬝ᵥ z) ^ γ)
      ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ)) = Mk.powerValue γ n) ∧
    ∀ αstar : ℕ → Fin d → ℝ,
      (∀ n < N, αstar n ∈ A n ∧ ∫⁻ z, ENNReal.ofReal ((1 + αstar n ⬝ᵥ z) ^ γ)
        ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ)) = Mk.powerValue γ n) →
      Mk.IsPolicy Es N (fun n x => (x + b * (S0 Mk.i n / S0 Mk.i N)) • αstar n) ∧
        ∀ x ∈ Es 0, Mk.Vpi U N (fun n x => (x + b * (S0 Mk.i n / S0 Mk.i N)) • αstar n) 0 x =
          Mk.V Es U N 0 x := by sorry

end BauerleRiederMDP.LQ.Supplement
