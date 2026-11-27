-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_4_2_4
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_4_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:52:03.758925+00:00
-- url     : https://prove2.me/theorems/ac96a832-5c9a-4df5-902a-ebf98914241c
-- title:
--   Theorem 4.2.4 — zero-mean returns: V_n(x) = U(x S^0_N/S^0_n) and investing only in the bond is optimal
-- statement:
--   Let $\mathbb E  R_n = 0$ for $n = 1, \dots , N$. Then it holds: a) the value functions are given by $V_n(x) = U(x S^0_N/S^0_n)$, $x \in  E$; b) the optimal portfolio strategy $(f^*_0, \dots , f^*_{N-1})$ is given by $f^*_n(x) ≡ 0$, i.e. the strategy "invest all the money in the bond" is optimal.
--
--   **Formalization Note.** The standing assumptions of §4.2 are kept: $dom U = [0, \infty )$ or $(0, \infty )$ and $E = dom U$, $U$ a utility function, independent returns and Assumption (FM), whose part (ii) makes $\mathbb E  R_n$ a genuine (Bochner) mean of an integrable vector. $\mathbb E  R_n = 0$ is componentwise. $S^0_n = \prod _{k=1}^n (1 + i_k)$ is the published `PartialObs.S0`. Optimality means $V_{0\pi }(x) = V_0(x)$ for $x \in  E$.
--
--   Differences from the source:
--   - encoding: 𝔼R_n = 0 → componentwise Bochner mean zero, integrable by (FM)(ii); reason: Lean convention; same statement
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.2.4, p.82 (PDF 96)

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

open MeasureTheory
open BauerleRiederMDP.NoArbitrage (IsUtilityFunction)
open BauerleRiederMDP.PartialObs (S0)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 4.2.4** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 4.2.4, p.82, PDF 96). Let `𝔼 R_n = 0` for `n = 1, …, N`. Then it holds:
a) the value functions are given by `V_n(x) = U(x S^0_N/S^0_n)`, `x ∈ E`;
b) the optimal portfolio strategy `(f*_0, …, f*_{N−1})` is given by `f*_n(x) ≡ 0`, i.e. the strategy
"invest all the money in the bond" is optimal.

**Formalization Note.** The standing assumptions of §4.2 are kept: `dom U = [0, ∞)` or `(0, ∞)` and
`E = dom U`, `U` a utility function, independent returns and Assumption (FM), whose part (ii)
makes `𝔼 R_n` a genuine (Bochner) mean of an integrable vector. `𝔼 R_n = 0` is componentwise.
`S^0_n = ∏_{k=1}^n (1 + i_k)` is the published `PartialObs.S0`. Optimality means
`V_{0π}(x) = V_0(x)` for `x ∈ E`. -/
theorem theorem_4_2_4 {d N : ℕ} (Mk : TWMarket d) (hFM : Mk.FM N) (dom : Set ℝ)
    (hdom : dom = Set.Ici 0 ∨ dom = Set.Ioi 0) (U : ℝ → ℝ) (hU : IsUtilityFunction dom U)
    (hmean : ∀ n, 1 ≤ n → n ≤ N → ∀ k, ∫ z, z k ∂(Mk.ν n : Measure (Fin d → ℝ)) = 0) :
    (∀ n ≤ N, ∀ x ∈ dom, Mk.V (fun _ => dom) U N n x = (U (x * (S0 Mk.i N / S0 Mk.i n)) : EReal)) ∧
    Mk.IsPolicy (fun _ => dom) N (fun _ _ => 0) ∧
    ∀ x ∈ dom, Mk.Vpi U N (fun _ _ => 0) 0 x = Mk.V (fun _ => dom) U N 0 x := by sorry

end BauerleRiederMDP.LQ.Supplement
