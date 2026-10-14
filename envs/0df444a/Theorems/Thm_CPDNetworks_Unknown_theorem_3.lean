-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_theorem_3
-- name    : CPDNetworks.Unknown.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:08.187265+00:00
-- url     : https://prove2.me/theorems/b5170473-16e4-433f-9e03-680d8764da65
-- title:
--   Theorem 3, p. 12 — above energy 4(1+ϵ)(6ω_n/T)^{1/2} + (C/√T) log(4n log₂T/(α∧β)) the dyadic-grid test has level α and type II error ≤ β
-- statement:
--   Consider $T$ independent snapshots of a network on $n$ vertices observed with missing links, with possible change of the connection-probability matrix at an unknown time $\tau\in\mathcal D_T=\{1,\dots,T-1\}$. For every $\epsilon\in(0,1/2]$ there are constants $C_\epsilon>0$ and $C$, depending only on $\epsilon$, such that the following holds for all $n\ge1$, $T\ge2$, $\omega_n\ge0$ and $\alpha,\beta\in(0,1)$. Let $\psi_{n,T}$ be the test (14) that rejects when $\max_{t\in\mathcal T}\|Z_T(t)\|_{2\to2}>H_{\alpha,n,T}$, where $\mathcal T$ is the dyadic grid (13), $Z_T$ the Matrix CUSUM and
--   $$H_{\alpha,n,T}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log\frac{4n\log_2(T)}{\alpha}.$$
--   If
--   $$R_{n,\mathcal D_T}\ \ge\ 4(1+\epsilon)\Big(\frac{6\omega_n}{T}\Big)^{1/2}+\frac{C}{\sqrt T}\log\Big(\frac{4n\log_2(T)}{\alpha\wedge\beta}\Big),$$
--   then
--   $$\alpha(\psi_{n,T})\le\alpha\qquad\text{and}\qquad\beta(\psi_{n,T},R_{n,\mathcal D_T})\le\beta,$$
--   the type I error being taken over $\mathcal S_n(\omega_n)$ and the type II error over every $\tau\in\mathcal D_T$ and every pair in $\mathcal W^\tau_{n,T}(\omega_n,R_{n,\mathcal D_T})$.
--
--   This is the paper's upper detection bound for an unknown change point: up to the factor $\sqrt6$ and the $\log\log T$ term it matches the rate $(\omega_n/T)^{1/2}$ attainable when the change time is known.
--
--   **Formalization Note.** Both constants are quantified existentially before $n$, $T$, $\omega_n$, $\alpha$, $\beta$ and $R$, so they cannot be tuned to the instance; the test inside the conclusion uses the same $C_\epsilon$ for both errors. The statement does not assume Lemma 12's predicate. $n\ge1$, $T\ge2$ and $\omega_n\ge0$ are the paper's implicit standing assumptions.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 12, Theorem 3 (test (14)–(15))

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Theorem 3, p. 12: for every `ϵ ∈ (0, 1/2]` there are constants `C_ϵ > 0` and `C`, depending
only on `ϵ`, such that the dyadic-grid test (14) with threshold (15) has type I error at most `α`
and type II error at most `β` over every change point `τ ∈ 𝒟_T` whenever
`R ≥ 4(1+ϵ)(6ω_n/T)^{1/2} + (C/√T) log(4n log₂T/(α ∧ β))`. -/
theorem theorem_3 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ Cε C : ℝ, 0 < Cε ∧
    ∀ (n T : ℕ) (ω α β R : ℝ), 1 ≤ n → 2 ≤ T → 0 ≤ ω →
      0 < α → α < 1 → 0 < β → β < 1 →
      4 * (1 + ε) * Real.sqrt (6 * ω / T) +
          C / Real.sqrt T * Real.log (4 * n * Real.logb 2 T / min α β) ≤ R →
      CPDNetworks.Lower.typeI (n := n) (T := T) ω (testGrid (thrGrid ε Cε ω α n T)) ≤ α ∧
      CPDNetworks.Lower.typeII (n := n) (T := T) (DT T) ω R (testGrid (thrGrid ε Cε ω α n T)) ≤ β := by sorry

end CPDNetworks.Unknown
