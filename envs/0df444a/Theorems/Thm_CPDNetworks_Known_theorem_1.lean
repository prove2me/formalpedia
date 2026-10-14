-- Prove2me | Theorems.Thm_CPDNetworks_Known_theorem_1
-- name    : CPDNetworks.Known.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:54.146223+00:00
-- url     : https://prove2.me/theorems/1bb59b11-037b-4227-a9eb-d52d9ebddcf1
-- title:
--   Theorem 1 — above energy $4\sqrt2(1+\epsilon)(\omega_n/T)^{1/2}+CT^{-1/2}\log(n/(\alpha\wedge\beta))$ the CUSUM test at $\tau$ has level $\alpha$ and type II error $\le\beta$
-- statement:
--   Let $\epsilon\in(0,1/2]$. There are constants $C_\epsilon>0$ and $C$, depending only on $\epsilon$, with the following property. Let $n\ge1$ be the number of vertices, $T$ the number of snapshots, $1\le\tau\le T-1$ the known candidate change point, $\omega_n\ge0$ the degree bound, and $\alpha,\beta\in(0,1)$. Let $\psi^\tau_{n,T}$ reject the null hypothesis when the spectral norm of the Matrix CUSUM at $\tau$ exceeds
--   $$H_{\alpha,n}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log(2n/\alpha).$$
--   If
--   $$R_{n,\tau}\ge4\sqrt2(1+\epsilon)\Big(\frac{\omega_n}{T}\Big)^{1/2}+\frac{C}{T^{1/2}}\log\Big(\frac{n}{\alpha\wedge\beta}\Big),$$
--   then
--   $$\alpha(\psi^\tau_{n,T})\le\alpha\qquad\text{and}\qquad\beta(\psi^\tau_{n,T},R_{n,\tau})\le\beta.$$
--
--   This is the upper detection boundary for a change at a known time: the energy $(\omega_n/T)^{1/2}$ matches, up to constants and the logarithmic term, the lower bound of Theorem 2 of the same paper.
--
--   **Formalization Note.** Both constants are chosen before $n$, $T$, $\tau$, $\omega_n$, $\alpha$, $\beta$ and $R_{n,\tau}$, and the threshold of the test uses the same $C_\epsilon$. The hypotheses $n\ge1$ and $\omega_n\ge0$ are implicit on the page ($n$ vertices, $\omega_n$ a degree bound). The statement does not assume the conclusion of Lemma 12: it asserts the existence of the constants outright.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 10, Theorem 1, display (12) (test (10), threshold (11))

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Known

/-- Theorem 1, p. 10: for every `ϵ ∈ (0, 1/2]` there are constants `C_ϵ > 0` (in the threshold
(11)) and `C` (in the energy condition (12)), chosen before `n, T, τ, ω_n, α, β, R`, such that
the Matrix CUSUM test (10) at the known location `τ` has type I error at most `α` and, whenever
`R ≥ 4√2(1+ϵ)(ω_n/T)^{1/2} + C T^{-1/2} log(n/(α ∧ β))`, type II error at most `β`. -/
theorem theorem_1 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ Cε C : ℝ, 0 < Cε ∧
      ∀ (n T τ : ℕ) (ω α β R : ℝ), 1 ≤ n → 1 ≤ τ → τ < T → 0 ≤ ω →
        0 < α → α < 1 → 0 < β → β < 1 →
        4 * Real.sqrt 2 * (1 + ε) * Real.sqrt (ω / T) +
            C / Real.sqrt T * Real.log (n / min α β) ≤ R →
        CPDNetworks.Lower.typeI (n := n) (T := T) ω (testKnown τ (thrKnown ε Cε ω α n)) ≤ α ∧
        CPDNetworks.Lower.typeII (n := n) (T := T) {τ} ω R (testKnown τ (thrKnown ε Cε ω α n)) ≤ β := by sorry

end CPDNetworks.Known
