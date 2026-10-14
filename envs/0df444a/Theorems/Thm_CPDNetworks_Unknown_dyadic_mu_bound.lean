-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_dyadic_mu_bound
-- name    : CPDNetworks.Unknown.dyadic_mu_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:58.148028+00:00
-- url     : https://prove2.me/theorems/e0b038ff-e9d1-4e4f-a54e-77c876c38a12
-- title:
--   Proof of Lemma 6, p. 32 — for every τ ∈ 𝒟_T some grid point t ∈ 𝒯 has μ^τ_T(t) ≥ (1/√3)√T q(τ/T)
-- statement:
--   Let $1\le\tau\le T-1$, let $\mu^\tau_T$ be the signal profile (7) and $\mathcal T$ the dyadic grid (13). Then some grid point captures at least a $1/\sqrt3$ fraction of the maximal signal $\mu^\tau_T(\tau)=\sqrt T\,q(\tau/T)$:
--   $$\exists\,t\in\mathcal T:\qquad\mu^\tau_T(t)\ \ge\ \frac1{\sqrt3}\sqrt T\,q(\tau/T).$$
--
--   This is why the test that only looks at the $O(\log T)$ grid points loses only a constant factor $\sqrt3$ in detection energy, for every unknown change point $\tau\in\mathcal D_T$.
--
--   **Formalization Note.** The paper's argument picks $t^*\in\mathcal T^L$ with $\tau/2\le t^*<\tau$ when $\tau\le T/2$; no such point exists for $\tau=1$, where $t^*=\tau=1$ works instead. The existence statement above is what the proof of Lemma 6 uses, and it is true for every $\tau\in\mathcal D_T$.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 32, proof of Lemma 6, paragraph "If τ ≤ T/2, there exists a t* ∈ 𝒯^L"

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Proof of Lemma 6, p. 32: for every change point `τ ∈ 𝒟_T` some grid point `t ∈ 𝒯` has
`μ^τ_T(t) ≥ √T CPDNetworks.Lower.q(τ/T) / √3`. -/
theorem dyadic_mu_bound (T τ : ℕ) (hτ : 1 ≤ τ) (hτT : τ < T) :
    ∃ t ∈ dyadicGrid T, 1 / Real.sqrt 3 * Real.sqrt T * CPDNetworks.Lower.q ((τ : ℝ) / T) ≤ CPDNetworks.Known.mu T τ t := by sorry

end CPDNetworks.Unknown
