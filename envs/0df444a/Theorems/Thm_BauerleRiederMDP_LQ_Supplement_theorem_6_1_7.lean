-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_6_1_7
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_6_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:57:13.659602+00:00
-- url     : https://prove2.me/theorems/a5c0824f-e3f0-4b0d-94ef-6b2818d32665
-- title:
--   Theorem 6.1.7 (corrected: x > 0 in part b) — logarithmic utility under partial observation: value log x + d_n(ρ) and myopic optimal strategy
-- statement:
--   Let $U$ be the logarithmic utility. Then a) the value functions are $J_n(x, \rho ) = \log (x) + d_n(\rho )$, $(x, \rho ) \in  E_X \times  \mathcal P(E_Y)$, where $(d_n)$ satisfies the recursion (6.6); b) the optimal amounts invested in the stocks are $f^*_n(x, \rho ) = \alpha ^*(\rho ) x$, where $\alpha ^*(\rho )$ is the solution of (6.6), and the optimal portfolio strategy is $(f_0, \dots , f_{N-1})$ with $f_n(h_n) := f^*_{N-n}(x_n, \mu _n(\cdot |h_n))$.
--
--   **Formalization Note.** $U = \log $ on $dom U = (0, \infty )$; the market, (FM), $D(x)$, the filter, $J_n$ (a supremum over policies of the filtered model, not the recursion), the problem (6.2) (`twValue`, a supremum over all observable strategies, admissibility almost sure) are the published `PartialObs` objects, and the hypothesis $hD$ (the sets $D(x)$ do not depend on $y$) is carried exactly as in the published Theorem 6.1.1. "$\alpha ^*(\rho )$ is the solution of (6.6)" is read as: a measurable $\alpha ^* : \mathcal P(E_Y) \to  \tilde A $ attaining $\sup _{\alpha  \in  \tilde A } \int \int  \log (1 + \alpha  \cdot  z) Q^R(dz|y) \rho (dy)$ (the only part of (6.6) depending on $\alpha $); its existence is stated, and b) holds for every such choice: for each $n \ge  1$, $(x, \rho ) \mapsto  \alpha ^*(\rho ) x$ is a maximizer of $J_{n-1}$, and the induced strategy is admissible and optimal for (6.2) from every initial wealth $x > 0$. The book's "$x \ge  0$" in b) is corrected to $x > 0$, the state space $E_X = dom U = (0, \infty )$.
--
--   Differences from the source:
--   - correction: f*_n(x,ρ) = α*(ρ)x, x ≥ 0 → x > 0; reason: x = 0 is outside the stated state space E_X = dom U = (0,∞), so the printed boundary is an index-domain slip
--   - reading: D(x) does not depend on y (remark on p.177) → the independence of the sets D(x) from y is a hypothesis, as in the published Theorem 6.1.1; reason: carries the published chunk's treatment of the remark on the open domain (0,∞)
--   - reading: α*(ρ) the solution of (6.6) → a measurable choice α* attaining the supremum; existence stated and b) for every such choice; reason: the solution need not be unique
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.1.7, p.182-183 (PDF 195)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_PartialObs_Market
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_filter
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
import Definitions.Def_BauerleRiederMDP_PartialObs_FM61
import Definitions.Def_BauerleRiederMDP_PartialObs_Dset
import Definitions.Def_BauerleRiederMDP_PartialObs_wealth
import Definitions.Def_BauerleRiederMDP_PartialObs_markovWealth
import Definitions.Def_BauerleRiederMDP_PartialObs_markovStrategy
import Definitions.Def_BauerleRiederMDP_PartialObs_twAdmissible
import Definitions.Def_BauerleRiederMDP_PartialObs_twValue
import Definitions.Def_BauerleRiederMDP_PartialObs_J
import Definitions.Def_BauerleRiederMDP_PartialObs_bellmanQ
import Definitions.Def_BauerleRiederMDP_PartialObs_IsMaximizer
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_AtildePos
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_logObj
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_dLog

open MeasureTheory
open BauerleRiederMDP.PartialObs
open BauerleRiederMDP.RegimeSwitching (eint)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 6.1.7** (corrected domain in part b; logarithmic utility under partial observation)
(Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), Theorem 6.1.7, pp.182–183, PDF 195–196,
setting of §6.1, pp.176–177, PDF 189–190). Let `U` be the logarithmic utility. Then
a) the value functions are `J_n(x, ρ) = log(x) + d_n(ρ)`, `(x, ρ) ∈ E_X × IP(E_Y)`, where `(d_n)`
satisfies the recursion (6.6);
b) the optimal amounts invested in the stocks are `f*_n(x, ρ) = α*(ρ) x`, where `α*(ρ)` is the
solution of (6.6), and the optimal portfolio strategy is `(f_0, …, f_{N−1})` with
`f_n(h_n) := f*_{N−n}(x_n, μ_n(·|h_n))`.

**Formalization Note.** `U = log` on `dom U = (0, ∞)`; the market, (FM), `D(x)`, the filter,
`J_n` (a supremum over policies of the filtered model, not the recursion), the problem (6.2)
(`twValue`, a supremum over all observable strategies, admissibility almost sure) are the published
`PartialObs` objects, and the hypothesis `hD` (the sets `D(x)` do not depend on `y`) is carried
exactly as in the published Theorem 6.1.1. "`α*(ρ)` is the solution of (6.6)" is read as: a
measurable `α* : IP(E_Y) → Ã` attaining `sup_{α ∈ Ã} ∫∫ log(1 + α · z) Q^R(dz|y) ρ(dy)` (the only
part of (6.6) depending on `α`); its existence is stated, and b) holds for every such choice: for
each `n ≥ 1`, `(x, ρ) ↦ α*(ρ) x` is a maximizer of `J_{n−1}`, and the induced strategy is admissible
and optimal for (6.2) from every initial wealth `x > 0`. The book's "`x ≥ 0`" in b) is corrected to
`x > 0`, the state space `E_X = dom U = (0, ∞)`. -/
theorem theorem_6_1_7 {EY : Type*} [MeasurableSpace EY] [StandardBorelSpace EY] {d : ℕ}
    (M : Market EY d) (i : ℝ) (hi : 0 ≤ i) (hFM : FM61 M)
    (hD : ∀ (x : ℝ) (y y' : EY),
      {a : Fin d → ℝ | ∀ᵐ z ∂M.QR y, (1 + i) * (x + a ⬝ᵥ z) ∈ Set.Ioi 0} =
        {a : Fin d → ℝ | ∀ᵐ z ∂M.QR y', (1 + i) * (x + a ⬝ᵥ z) ∈ Set.Ioi 0}) :
    -- a)
    (∀ (n : ℕ) (x : ℝ) (ρ : ProbabilityMeasure EY), 0 < x →
      J M i (Set.Ioi 0) Real.log n x ρ = ((Real.log x : ℝ) : EReal) + dLog M i n ρ) ∧
    -- b) existence of α*
    (∃ α : ProbabilityMeasure EY → Fin d → ℝ, Measurable α ∧
      ∀ ρ, α ρ ∈ AtildePos M ∧ logObj M ρ (α ρ) = ⨆ a ∈ AtildePos M, logObj M ρ a) ∧
    -- b) every such α* gives maximizers and an optimal strategy
    (∀ α : ProbabilityMeasure EY → Fin d → ℝ,
      (Measurable α ∧
        ∀ ρ, α ρ ∈ AtildePos M ∧ logObj M ρ (α ρ) = ⨆ a ∈ AtildePos M, logObj M ρ a) →
      (∀ n : ℕ, 1 ≤ n →
        IsMaximizer M i (Set.Ioi 0) (J M i (Set.Ioi 0) Real.log (n - 1)) (fun p => p.1 • α p.2)) ∧
      ∀ (N : ℕ) (x : ℝ), 0 < x →
        twAdmissible M i (Set.Ioi 0) N x
            (markovStrategy M (fun _ => i) x M.Q0 (fun _ p => p.1 • α p.2)) ∧
          eint (M.returnLaw M.Q0 N) (fun r => ((Real.log (wealth (fun _ => i) x
              (markovStrategy M (fun _ => i) x M.Q0 (fun _ p => p.1 • α p.2)) N r) : ℝ) :
                EReal)) = twValue M i (Set.Ioi 0) Real.log N x) := by sorry

end BauerleRiederMDP.LQ.Supplement
