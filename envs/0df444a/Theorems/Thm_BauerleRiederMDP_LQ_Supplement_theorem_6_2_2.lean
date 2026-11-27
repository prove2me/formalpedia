-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_6_2_2
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_6_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:58:05.765143+00:00
-- url     : https://prove2.me/theorems/38b98bde-1f92-430d-bb26-b54f1cfa6b83
-- title:
--   Theorem 6.2.2 (corrected: second moments in (FM)) — QP(b) under partial observation: value, optimal strategy, first two moments
-- statement:
--   For the solution of the Markov Decision Problem QP(b) it holds: a) the value functions are $V_n(x, \rho ) = (x S^0_N / S^0_n - b)^2 d_n(\rho )$, with $(d_n)$ of (6.7), and $V_0(x_0, Q_0)$ is the value of QP(b); b) with $f^*_n(x, \rho ) = (b S^0_n / S^0_N - x) C_{n+1}(\rho )^{-1} \ell _{n+1}(\rho )$, the portfolio strategy $\pi ^* = (f_0, \dots , f_{N-1})$, $f_n(h_n) := f^*_n(x_n, \mu _n(\cdot |h_n))$, is optimal for QP(b); c) $\mathbb E ^{\pi ^*}_{x_0}[X_N] = x_0 S^0_N d_0(Q_0) + b(1 - d_0(Q_0))$ and $\mathbb E ^{\pi ^*}_{x_0}[X_N^2] = (x_0 S^0_N)^2 d_0(Q_0) + b^2(1 - d_0(Q_0))$.
--
--   **Formalization Note.** The market, Assumption (FM) of §6.2 (the published $FM62$, with second moments bounded uniformly in $y$), $S^0_n$, the filter and the functions $\underline{d}$, $\ell $, $C$, $d$ of (6.7) are the published `PartialObs` objects; the book's $d_n$ for horizon $N$ is `dSeq M (N − n)` (stages to go). $V_n$ is `qpValue`, an infimum over all history-dependent policies from time $n$, for $n \le  N$. Assumption (FM)(iv), $x_0 S^0_N < \mu $, concerns the mean-variance level $\mu $, which does not occur in QP(b). In b) and c) $\pi ^*$ is the published `markovStrategy` started from $(x_0, Q_0)$; optimality is $\mathbb E [(X_N - b)^2] = V_0(x_0, Q_0)$, the moments are Bochner integrals under the market law `M.returnLaw M.Q0 N`, and $X_N$ is square integrable.
--
--   Differences from the source:
--   - correction: (FM)(i) sup_y 𝔼‖R(y)‖ < ∞ → sup_y 𝔼‖R(y)‖² < ∞ (published FM62); reason: with infinite second moments C_n(ρ) = ∫∫ d_n z zᵀ is infinite and (6.7) is undefined, so the value formula has no meaning
--   - reading: (FM)(iv) x_0 S^0_N < μ → not assumed; reason: it concerns the mean-variance level μ, which does not occur in QP(b)
--   - encoding: d_n for horizon N → dSeq M (N − n) (stages to go); reason: published indexing; same functions
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.2.2, p.186 (PDF 199)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_filter
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
import Definitions.Def_BauerleRiederMDP_PartialObs_FM62
import Definitions.Def_BauerleRiederMDP_PartialObs_wealth
import Definitions.Def_BauerleRiederMDP_PartialObs_markovWealth
import Definitions.Def_BauerleRiederMDP_PartialObs_markovStrategy
import Definitions.Def_BauerleRiederMDP_PartialObs_S0
import Definitions.Def_BauerleRiederMDP_PartialObs_dUnder
import Definitions.Def_BauerleRiederMDP_PartialObs_ell
import Definitions.Def_BauerleRiederMDP_PartialObs_Cmat
import Definitions.Def_BauerleRiederMDP_PartialObs_dSeq
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_qpValue

open MeasureTheory
open BauerleRiederMDP.PartialObs
open Matrix

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 6.2.2** (QP(b) under partial observation) (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Theorem 6.2.2, p.186, PDF 199, setting of §6.2,
pp.184–185, PDF 197–198). For the solution of the Markov Decision Problem QP(b) it holds:
a) the value functions are `V_n(x, ρ) = (x S^0_N / S^0_n − b)² d_n(ρ)`, with `(d_n)` of (6.7), and
`V_0(x_0, Q_0)` is the value of QP(b);
b) with `f*_n(x, ρ) = (b S^0_n / S^0_N − x) C_{n+1}(ρ)^{−1} ℓ_{n+1}(ρ)`, the portfolio strategy
`π* = (f_0, …, f_{N−1})`, `f_n(h_n) := f*_n(x_n, μ_n(·|h_n))`, is optimal for QP(b);
c) `𝔼^{π*}_{x_0}[X_N] = x_0 S^0_N d_0(Q_0) + b(1 − d_0(Q_0))` and
`𝔼^{π*}_{x_0}[X_N²] = (x_0 S^0_N)² d_0(Q_0) + b²(1 − d_0(Q_0))`.

**Formalization Note.** The market, Assumption (FM) of §6.2 (the published `FM62`, with second
moments bounded uniformly in `y`), `S^0_n`, the filter and the functions `d̲`, `ℓ`, `C`, `d` of (6.7)
are the published `PartialObs` objects; the book's `d_n` for horizon `N` is `dSeq M (N − n)` (stages
to go). `V_n` is `qpValue`, an infimum over all history-dependent policies from time `n`, for
`n ≤ N`. Assumption (FM)(iv), `x_0 S^0_N < μ`, concerns the mean-variance level `μ`, which does
not occur in QP(b). In b) and c) `π*` is the published `markovStrategy` started from `(x_0, Q_0)`;
optimality is `𝔼[(X_N − b)²] = V_0(x_0, Q_0)`, the moments are Bochner integrals under the market
law `M.returnLaw M.Q0 N`, and `X_N` is square integrable. -/
theorem theorem_6_2_2 {EY : Type*} [MeasurableSpace EY] [StandardBorelSpace EY] {d : ℕ}
    (M : Market EY d) (i : ℕ → ℝ) (hi : ∀ n, 0 ≤ i n) (hFM : FM62 M) (N : ℕ) (b : ℝ) :
    let fstar : ℕ → ℝ × ProbabilityMeasure EY → Fin d → ℝ := fun n p =>
      (b * S0 i n / S0 i N - p.1) •
        ((Cmat M (dSeq M (N - (n + 1))) p.2)⁻¹ *ᵥ ell M (dSeq M (N - (n + 1))) p.2)
    -- a)
    (∀ (n : ℕ) (x : ℝ) (ρ : ProbabilityMeasure EY), n ≤ N →
      qpValue M i N b n x ρ =
        ENNReal.ofReal ((x * S0 i N / S0 i n - b) ^ 2 * dSeq M (N - n) ρ)) ∧
    -- b) and c)
    (∀ x0 : ℝ,
      let πstar := markovStrategy M i x0 M.Q0 fstar
      let P := M.returnLaw M.Q0 N
      let X := wealth i x0 πstar N
      (∀ k < N, Measurable (πstar k)) ∧ MemLp X 2 P ∧
        ∫⁻ r, ENNReal.ofReal ((X r - b) ^ 2) ∂P = qpValue M i N b 0 x0 M.Q0 ∧
        ∫ r, X r ∂P = x0 * S0 i N * dSeq M N M.Q0 + b * (1 - dSeq M N M.Q0) ∧
        ∫ r, X r ^ 2 ∂P = (x0 * S0 i N) ^ 2 * dSeq M N M.Q0 + b ^ 2 * (1 - dSeq M N M.Q0)) := by sorry

end BauerleRiederMDP.LQ.Supplement
