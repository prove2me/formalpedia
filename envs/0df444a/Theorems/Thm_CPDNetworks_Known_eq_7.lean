-- Prove2me | Theorems.Thm_CPDNetworks_Known_eq_7
-- name    : CPDNetworks.Known.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:35.743184+00:00
-- url     : https://prove2.me/theorems/e844bac0-7f51-4b00-82bb-990367741a29
-- title:
--   Display (7), p. 8 — $Z_T(t)=-\mu^\tau_T(t)\,\Pi\odot\Delta\Theta^\tau+\xi(t)$, and $\mu^\tau_T$ peaks at $\tau$ with value $\sqrt T q(\tau/T)$
-- statement:
--   Fix $1\le\tau\le T-1$, matrices $\Theta^a,\Theta^b,\Pi$, and let $B^s=\Pi\odot\Theta^b$ for $s\le\tau$ and $B^s=\Pi\odot\Theta^a$ for $s>\tau$ be the edge probabilities of the alternative with a change at $\tau$. Write $\Delta\Theta^\tau=\Theta^a-\Theta^b$. Then:
--
--   1. for every observation $Y$ and every $1\le t\le T-1$,
--   $$Z_T(t)=-\mu^\tau_T(t)\,\Pi\odot\Delta\Theta^\tau+\xi(t),$$
--   where $\xi(t)$ is the CUSUM of the centred matrices $Y^s-B^s$;
--   2. $\mu^\tau_T(t)\le\mu^\tau_T(\tau)$ for every $1\le t\le T-1$;
--   3. $\mu^\tau_T(\tau)=\sqrt T\,q(\tau/T)$, with $q(x)=\sqrt{x(1-x)}$.
--
--   The decomposition separates the Matrix CUSUM into a deterministic signal, largest at the true change point, and a centred noise process; both the level and the power analysis of the test start from it.
--
--   **Formalization Note.** The identity is stated pathwise, for every observation, so it holds under the alternative law and, with $\Theta^a=\Theta^b$, under the null.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 8, display (7) and the sentence after (8)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Known

/-- Display (7), p. 8: pathwise signal-plus-noise decomposition of the Matrix CUSUM under the
alternative law, and the maximum of `μ^τ_T` at the true change point. -/
theorem eq_7 {n T : ℕ} (τ : ℕ) (hτ1 : 1 ≤ τ) (hτT : τ < T)
    (Θa Θb Pm : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (y : CPDNetworks.Lower.Obs n T) (t : ℕ), 1 ≤ t → t < T →
      CPDNetworks.Lower.cusum y t = -(mu T τ t) • (Pm ⊙ (Θa - Θb)) + noise (CPDNetworks.Lower.altParam τ Θa Θb Pm) y t) ∧
    (∀ t : ℕ, 1 ≤ t → t < T → mu T τ t ≤ mu T τ τ) ∧
    mu T τ τ = Real.sqrt T * CPDNetworks.Lower.q ((τ : ℝ) / T) := by sorry

end CPDNetworks.Known
