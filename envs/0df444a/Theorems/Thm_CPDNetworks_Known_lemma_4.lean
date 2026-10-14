-- Prove2me | Theorems.Thm_CPDNetworks_Known_lemma_4
-- name    : CPDNetworks.Known.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:28.180207+00:00
-- url     : https://prove2.me/theorems/22ce41de-3124-4d83-94b2-c9910bf6c308
-- title:
--   Lemma 4 — under (24) the type II error of test (10) is at most $\beta$
-- statement:
--   Let $\epsilon\in(0,1/2]$ and let $C_\epsilon>0$ be a constant for which the conclusion (38) of Lemma 12 holds. Let $n\ge1$, $1\le\tau\le T-1$, $\omega_n\ge0$, $\alpha,\beta\in(0,1)$, and let $H_{\alpha,n}$ be given by (11). Suppose that
--   $$R_{n,\tau}\ge4\sqrt2(1+\epsilon)\Big(\frac{\omega_n}{T}\Big)^{1/2}+\frac{C_\epsilon}{\sqrt T}\Big(\log\frac{2n}{\alpha}+\log\frac{2n}{\beta}\Big).$$
--   Then the type II error of the test (10) at the known location $\tau$ is at most $\beta$:
--   $$\beta(\psi^\tau_{n,T},R_{n,\tau})=\sup_{\mathcal W^\tau_{n,T}(\omega_n,R_{n,\tau})}\mathbb P_{(\Theta^0+\Delta\Theta^\tau,\Pi),(\Theta^0,\Pi)}\big\{\|Z_T(\tau)\|_{2\to2}\le H_{\alpha,n}\big\}\le\beta.$$
--
--   This is the power half of Theorem 1.
--
--   **Formalization Note.** The page prints $(\kappa_n/T)^{1/2}$ in (24); the proof's last displays use $\omega_n^{1/2}$ and $\kappa_n$ is not a parameter of the testing problem, so the statement uses $\omega_n$. "$C_\epsilon$ is the constant of Lemma 12" is a hypothesis.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 31, Lemma 4, display (24)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Known

/-- Lemma 4, p. 31: with `C_ϵ` a constant of Lemma 12, if
`R ≥ 4√2(1+ϵ)(ω_n/T)^{1/2} + C_ϵ T^{-1/2}(log(2n/α) + log(2n/β))` (display (24), with the
page's `κ_n` read as `ω_n`), the test (10) with threshold (11) has type II error at most `β`
at the known location `τ`. -/
theorem lemma_4 (ε Cε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : 0 < Cε)
    (hnoise : IsNoiseConst ε Cε)
    (n T τ : ℕ) (ω α β R : ℝ) (hn : 1 ≤ n) (hτ1 : 1 ≤ τ) (hτT : τ < T) (hω : 0 ≤ ω)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hR : 4 * Real.sqrt 2 * (1 + ε) * Real.sqrt (ω / T) +
        Cε / Real.sqrt T * (Real.log (2 * n / α) + Real.log (2 * n / β)) ≤ R) :
    CPDNetworks.Lower.typeII (n := n) (T := T) {τ} ω R (testKnown τ (thrKnown ε Cε ω α n)) ≤ β := by sorry

end CPDNetworks.Known
