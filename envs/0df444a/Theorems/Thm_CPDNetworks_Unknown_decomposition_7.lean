-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_decomposition_7
-- name    : CPDNetworks.Unknown.decomposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:41.93098+00:00
-- url     : https://prove2.me/theorems/a479ee91-6c82-4aa5-b41c-12a4d892627f
-- title:
--   (7), p. 8 — Z_T(t) = −μ^τ_T(t) Π ⊙ ΔΘ^τ + ξ(t), and μ^τ_T is maximal, equal to √T q(τ/T), at t = τ
-- statement:
--   Fix $n$ vertices, a horizon $T$ and a change point $\tau$ with $1\le\tau\le T-1$. Let $\Theta^b$ (before) and $\Theta^a$ (after) be $n\times n$ matrices and $\Pi$ a sampling matrix, write $\Delta\Theta^\tau=\Theta^a-\Theta^b$, and let $B^s=\Pi\odot\Theta^b$ for $s\le\tau$ and $B^s=\Pi\odot\Theta^a$ for $s>\tau$. For every realisation $Y$ of the observations, let $Z_T(t)$ be the Matrix CUSUM (6) and $\xi(t)$ the noise process (8) built from $X^s=Y^s-B^s$. Then:
--
--   1. for every $1\le t\le T-1$,
--   $$Z_T(t)=-\mu^\tau_T(t)\,\Pi\odot\Delta\Theta^\tau+\xi(t),$$
--   with $\mu^\tau_T(t)=\sqrt{t(T-t)/T}\,\big(\tfrac\tau t\mathbf 1_{\{\tau+1\le t\le T\}}+\tfrac{T-\tau}{T-t}\mathbf 1_{\{1\le t\le\tau\}}\big)$;
--   2. $\mu^\tau_T(\tau)=\sqrt T\,q(\tau/T)$, where $q(x)=\sqrt{x(1-x)}$;
--   3. $\mu^\tau_T(t)\le\mu^\tau_T(\tau)$ for every $1\le t\le T-1$.
--
--   The identity splits the CUSUM into a deterministic signal, proportional to the jump $\Pi\odot\Delta\Theta^\tau$, and centred noise; it is the starting point of the power analysis of every CUSUM-based test of the paper.
--
--   **Formalization Note.** The identity is stated pathwise, for every observation, so no probability enters. Time is 0-based in Lean, and the alternative's parameters are those of the Setting file.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 8, display (7) and the sentence after (8)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Display (7), p. 8: under the alternative the matrix CUSUM is `−μ^τ_T(t) Π ⊙ ΔΘ^τ + ξ(t)`
pathwise, and `μ^τ_T` attains its maximum `√T CPDNetworks.Lower.q(τ/T)` over `1 ≤ t ≤ T − 1` at `t = τ`. -/
theorem decomposition_7 (n T τ : ℕ) (Θa Θb Pi : Matrix (Fin n) (Fin n) ℝ)
    (hτ : 1 ≤ τ) (hτT : τ < T) :
    (∀ (y : CPDNetworks.Lower.Obs n T) (t : ℕ), 1 ≤ t → t < T →
      CPDNetworks.Lower.cusum y t = -(CPDNetworks.Known.mu T τ t) • (Pi ⊙ (Θa - Θb)) + CPDNetworks.Known.noise (CPDNetworks.Lower.altParam τ Θa Θb Pi) y t) ∧
    CPDNetworks.Known.mu T τ τ = Real.sqrt T * CPDNetworks.Lower.q ((τ : ℝ) / T) ∧
    (∀ t : ℕ, 1 ≤ t → t < T → CPDNetworks.Known.mu T τ t ≤ CPDNetworks.Known.mu T τ τ) := by sorry

end CPDNetworks.Unknown
