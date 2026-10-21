-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_existence_ivt
-- name    : CostlyPriceInterp.MarketEq.existence_ivt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:31.754696+00:00
-- url     : https://prove2.me/theorems/344f4a61-5f3a-4305-bdab-5b48e335c60e
-- title:
--   Proof of Proposition 1, p. 56 — f(0) = −τ_eτ_u < 0 < f(ᾱ), so f has a root in (0, ᾱ)
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$. Let $f$ be the cubic of (18) and
--   $$\bar\alpha = \frac{\tau_e\tau_u}{\tau_e\tau_\varepsilon+\tau_e\tau_\eta+\tau_u\tau_\varepsilon}.$$
--   Then $f(0) = -\tau_e\tau_u < 0$, $f(\bar\alpha) > 0$, and there exists $\alpha\in(0,\bar\alpha)$ with $f(\alpha) = 0$.
--
--   This is the existence half of Proposition 1: a positive root of (18), and hence a linear equilibrium, exists in the interval $(0,\bar\alpha)$.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 56 (PDF 55), proof of Proposition 1, 'We can compute f(0) = −τ_eτ_u < 0 and f(τ_eτ_u/(τ_eτ_ε + τ_eτ_η + τ_uτ_ε)) > 0, and thus by the Intermediate Value Theorem …'

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 56 (PDF 55): f(0) = −τ_eτ_u < 0, f(ᾱ) > 0 with
ᾱ = τ_eτ_u/(τ_eτ_ε + τ_eτ_η + τ_uτ_ε), and hence f has a root in (0, ᾱ). -/
theorem existence_ivt (P : Params) (hP : P.Standing) :
    cubicF P 0 = -(P.te * P.tu) ∧ cubicF P 0 < 0 ∧ 0 < cubicF P (alphaBar P) ∧
      ∃ α ∈ Set.Ioo 0 (alphaBar P), cubicF P α = 0 := by sorry
end CostlyPriceInterp.MarketEq
