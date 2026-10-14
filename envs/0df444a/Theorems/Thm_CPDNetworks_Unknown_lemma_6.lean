-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_lemma_6
-- name    : CPDNetworks.Unknown.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:00.020388+00:00
-- url     : https://prove2.me/theorems/c4e70c71-0cac-4a09-a19e-9e1767d07b9d
-- title:
--   Lemma 6, p. 32 — above energy 4√6(1+ϵ)(ω_n/T)^{1/2} + (√3C_ϵ/√T)(log(4n log₂T/α) + log(2n/β)) the type II error is ≤ β
-- statement:
--   Fix $\epsilon\in(0,1/2]$ and let $C_\epsilon$ be a constant for which the noise bound of Lemma 12 holds. Let $n\ge1$, $T\ge2$, $\omega_n\ge0$, $\alpha,\beta\in(0,1)$, and let $\psi_{n,T}$ be the dyadic-grid test (14) with threshold $H_{\alpha,n,T}$ of (15). If
--   $$R_{n,\mathcal D_T}\ \ge\ 4\sqrt6(1+\epsilon)\Big(\frac{\omega_n}{T}\Big)^{1/2}+\frac{\sqrt3\,C_\epsilon}{\sqrt T}\Big(\log\frac{4n\log_2(T)}{\alpha}+\log\frac{2n}{\beta}\Big),$$
--   then the type II error of $\psi_{n,T}$, over every change point $\tau\in\mathcal D_T=\{1,\dots,T-1\}$ and every pair $\{(\Theta^a,\Pi),(\Theta^b,\Pi)\}\in\mathcal W^\tau_{n,T}(\omega_n,R_{n,\mathcal D_T})$, is at most $\beta$:
--   $$\beta(\psi_{n,T},R_{n,\mathcal D_T})=\sup_{\tau\in\mathcal D_T}\ \sup_{\mathcal W^\tau_{n,T}(\omega_n,R_{n,\mathcal D_T})}\mathrm P\{\psi_{n,T}=0\}\le\beta.$$
--
--   The test inspects only the grid points, while the change may occur at any $\tau\in\mathcal D_T$; the factor $\sqrt3$ in the energy is the price of the grid.
--
--   **Formalization Note.** "$C_\epsilon$ is a constant of Lemma 12" is a hypothesis (the predicate of the Setting file). The supremum over $\tau$ ranges over all of $\mathcal D_T$, not over the grid. $n\ge1$, $T\ge2$ and $\omega_n\ge0$ are the paper's implicit standing assumptions.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 32, Lemma 6 (with (14)–(15), p. 12)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Lemma 6, p. 32: above the energy `4√6(1+ϵ)(ω_n/T)^{1/2} + (√3 C_ϵ/√T)(log(4n log₂T/α) + log(2n/β))`
the type II error of the dyadic-grid test, over all change points `τ ∈ 𝒟_T`, is at most `β`. -/
theorem lemma_6 (ε Cε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : CPDNetworks.Known.IsNoiseConst ε Cε)
    (n T : ℕ) (ω α β R : ℝ) (hn : 1 ≤ n) (hT : 2 ≤ T) (hω : 0 ≤ ω)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hR : 4 * Real.sqrt 6 * (1 + ε) * Real.sqrt (ω / T) +
        Real.sqrt 3 * Cε / Real.sqrt T *
          (Real.log (4 * n * Real.logb 2 T / α) + Real.log (2 * n / β)) ≤ R) :
    CPDNetworks.Lower.typeII (n := n) (T := T) (DT T) ω R (testGrid (thrGrid ε Cε ω α n T)) ≤ β := by sorry

end CPDNetworks.Unknown
