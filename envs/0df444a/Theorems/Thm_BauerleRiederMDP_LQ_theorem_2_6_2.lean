-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_theorem_2_6_2
-- name    : BauerleRiederMDP.LQ.theorem_2_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:24:21.890925+00:00
-- url     : https://prove2.me/theorems/05ad0941-a087-4d62-809a-96afb8a59ba5
-- title:
--   Theorem 2.6.2 — the cash balance problem has critical levels $S_{n-}\le S_{n+}$ and the control-band policy (2.6) is optimal
-- statement:
--   Consider the cash balance problem with transfer cost $c(z)=c_uz^++c_dz^-$ ($c_u,c_d>0$), convex holding cost $L\ge0$ with $L(0)=0$ and $L(x)/|x|\to\infty$ as $|x|\to\infty$, i.i.d. integrable cash changes $Z$, discount factor $\beta\in(0,1]$ and horizon $N$, and let $J_n$ be the minimal expected discounted cost over $n$ stages.
--
--   1. There exist critical levels $S_{n-}\le S_{n+}$ such that for $n=1,\dots,N$
--   $$
--   J_n(x)=\begin{cases}(S_{n-}-x)c_u+L(S_{n-})+\beta\,\mathbb E\,J_{n-1}(S_{n-}-Z)&x<S_{n-},\\ L(x)+\beta\,\mathbb E\,J_{n-1}(x-Z)&S_{n-}\le x\le S_{n+},\\ (x-S_{n+})c_d+L(S_{n+})+\beta\,\mathbb E\,J_{n-1}(S_{n+}-Z)&x>S_{n+},\end{cases}
--   $$
--   with $J_0\equiv0$.
--   2. The policy $(f^*_N,\dots,f^*_1)$ is optimal, where
--   $$
--   f^*_n(x)=\begin{cases}S_{n-}&x<S_{n-},\\ x&S_{n-}\le x\le S_{n+},\\ S_{n+}&x>S_{n+}\end{cases}
--   $$
--   with the levels of part 1: its expected discounted cost over $N$ stages equals $J_N(x)$ for every initial cash level $x$.
--
--   The optimal policy is a control band: below $S_{n-}$ the firm sells securities to raise cash to $S_{n-}$, above $S_{n+}$ it buys securities to lower cash to $S_{n+}$, and in between it does nothing.
--
--   **Formalization Note** $J_n$ is minus the reward value of the published stationary Markov Decision Model (Remark 2.3.15); $\mathbb E\,J_{n-1}(y-Z)$ is the extended-real integral of that model's operator layer against the law of $Z$. The policy $(f^*_N,\dots,f^*_1)$ uses $f^*_{N-k}$ at time $k=0,\dots,N-1$, and part 2 holds for every policy whose rules at times $k<N$ are these.
--
--   Differences from the source:
--   - generalization: the levels of a) are not stated to be ordered → Lean asserts $S_{n-}\le S_{n+}$; reason: the rule (2.6) is of the form (2.5) defining $\Delta$, which requires $S_-\le S_+$, and the book derives it on p.48; the statement without it follows.
--   - encoding: $J_n$ is the minimal expected discounted cost → minus the published stationary reward value `J`; reason: Remark 2.3.15, cost $=$ negative reward; values in extended reals.
--   - encoding: $\mathbb E\,J_{n-1}(y-Z)$ → `erealIntegral` of $z\mapsto J_{n-1}(y-z)$ against $\mu_Z$; reason: the integrand is extended-real valued; for the nonnegative $J_{n-1}$ it is the Lebesgue integral.
--   - encoding: "$(f^*_N,\dots,f^*_1)$ is optimal" → every $\pi$ with $\pi_k=f^*_{N-k}$ for $k<N$ has $J_{N\pi}(x)=J_N(x)$ for all $x$; reason: the book's definition of an optimal policy (p.18, §2.5) with time running forward.
--   - encoding: $\lim_{|x|\to\infty}L(x)/|x|=\infty$ → limit along the cocompact filter; "finite expectation" → `Integrable id μZ`; reason: same conditions.
--   - reading: "The optimal cash balance policy is given by" → every policy with these rules at times $k<N$ is optimal, no uniqueness; reason: a policy can be changed at states it never reaches: for $Z\equiv0$, $N=2$, $X_1$ stays in $[S_{2-},S_{2+}]$, so $f_1$ can be changed outside that band without changing $J_{2\pi}$.
--   - encoding: i.i.d. $(Z_n)$ → one law $\mu_Z$ in the stationary transition kernel; reason: the book's data list ($Q^Z$ := distribution of $Z_{n+1}$, independent of $(x,a)$) and Theorem 2.1.3.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.6.2, p.49 (PDF 64); model §2.6.2, pp.46–47 (PDF 61–62)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction
import Definitions.Def_BauerleRiederMDP_LQ_CashBalance

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ

/-- **Theorem 2.6.2** (Bäuerle & Rieder 2011, p.49, PDF 64), the cash balance problem of §2.6.2
(pp.46–49, PDF 61–64), with planning horizon `N`.

a) There exist critical levels `S_{n−}` and `S_{n+}` such that for `n = 1, …, N`
`J_n(x) = (S_{n−} − x) c_u + L(S_{n−}) + β 𝔼 J_{n−1}(S_{n−} − Z)` if `x < S_{n−}`,
`J_n(x) = L(x) + β 𝔼 J_{n−1}(x − Z)` if `S_{n−} ≤ x ≤ S_{n+}`,
`J_n(x) = (x − S_{n+}) c_d + L(S_{n+}) + β 𝔼 J_{n−1}(S_{n+} − Z)` if `x > S_{n+}`, with `J_0 ≡ 0`.

b) The optimal cash balance policy is given by `(f*_N, …, f*_1)` where `f*_n(x) := S_{n−}` if
`x < S_{n−}`, `x` if `S_{n−} ≤ x ≤ S_{n+}`, `S_{n+}` if `x > S_{n+}` (2.6), with the levels of a).

The statement also records `S_{n−} ≤ S_{n+}` (the form (2.5) of the set `Δ`, p.49).

**Formalization Note.** `J_n` is the minimal expected discounted cost `CashBalanceData.Jcost`
(minus the reward value `MDPFinance.Stationary.J` of `CashBalanceData.toSMDP`, Remark 2.3.15).
`𝔼 J_{n−1}(y − Z)` is the extended-real integral `MDPFinance.Stationary.erealIntegral` against the law
`μZ` of `Z`. The policy `(f*_N, …, f*_1)` uses `f*_{N−k}` at time `k = 0, …, N − 1`; it is optimal
when its expected discounted cost over `N` stages equals `J_N` in every state (the book's
definition of optimality, p.18). -/
theorem theorem_2_6_2 (M : CashBalanceData) (N : ℕ) :
    (∀ x : ℝ, M.Jcost 0 x = 0) ∧
    ∃ Sm Sp : ℕ → ℝ,
      (∀ n, 1 ≤ n → n ≤ N → Sm n ≤ Sp n ∧ ∀ x : ℝ, M.Jcost n x =
        if x < Sm n then
          (((Sm n - x) * M.cu + M.L (Sm n) : ℝ) : EReal) + (M.β : EReal) *
            MDPFinance.Stationary.erealIntegral (M.μZ : Measure ℝ)
              (fun z => M.Jcost (n - 1) (Sm n - z))
        else if x ≤ Sp n then
          ((M.L x : ℝ) : EReal) + (M.β : EReal) *
            MDPFinance.Stationary.erealIntegral (M.μZ : Measure ℝ)
              (fun z => M.Jcost (n - 1) (x - z))
        else
          (((x - Sp n) * M.cd + M.L (Sp n) : ℝ) : EReal) + (M.β : EReal) *
            MDPFinance.Stationary.erealIntegral (M.μZ : Measure ℝ)
              (fun z => M.Jcost (n - 1) (Sp n - z))) ∧
      ∀ π : ℕ → ℝ → ℝ, (∀ k < N, π k = cbRule (Sm (N - k)) (Sp (N - k))) →
        ∀ x : ℝ, M.JcostPi π N x = M.Jcost N x := by sorry

end BauerleRiederMDP.LQ
