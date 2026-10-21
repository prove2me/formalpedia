-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_model_facts
-- name    : BleedFeed.ControlLimit.model_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:45.416252+00:00
-- url     : https://prove2.me/theorems/f0847d6f-5e83-4e0f-8fd0-f34faf9f7807
-- title:
--   §3, p. 12 — $p_{i\mu}=1$ before the critical age, strictly decreasing from it on, and $\tilde\imath_\mu$ nonincreasing in $\mu$
-- statement:
--   Consider the bleed–feed model with standing assumptions (see the definition file): biomass $m_{i\mu}=m_0(1+\mu\tau)^i$, survival probability $p_{i\mu}=1-\nu(m_{i\mu})\tau$, where $\nu$ vanishes up to the critical biomass $\tilde m$ and increases strictly beyond it, and critical age $\tilde\imath_\mu$, the least $i$ with $m_{i\mu}>\tilde m$. For every growth rate $\mu\in\mathcal M=[\mu_\ell,\mu_u]$:
--
--   1. $p_{i\mu}=1$ for all $i<\tilde\imath_\mu$;
--   2. $p_{i-1,\mu}>p_{i\mu}$ for all $i\ge\tilde\imath_\mu$ with $i\ge 1$;
--   3. for every $\mu^+\in\mathcal M$ with $\mu\le\mu^+$,
--   $$
--   \tilde\imath_{\mu^+}\le\tilde\imath_\mu .
--   $$
--
--   These are the facts about the risk profile that every structural result of §4 uses: there is no risk before the critical age, the risk grows strictly afterwards, and faster cultures reach the critical age no later.
--
--   **Formalization Note** The clause $i\ge 1$ in item 2 excludes $i=\tilde\imath_\mu=0$, where the page's index $i-1=-1$ is undefined.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 12, §3 (critical-biomass paragraph), 'Hence, p_iµ = 1 for i < ĩ_µ, and p_{i−1µ} > p_iµ for i ≥ ĩ_µ. Clearly, by (1), the critical age ĩ_µ is nonincreasing in µ.'

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- §3, p. 12: for µ ∈ ℳ, p_iµ = 1 for i < ĩ_µ; p_{i−1,µ} > p_iµ for i ≥ ĩ_µ (and i ≥ 1);
and the critical age ĩ_µ is nonincreasing in µ on ℳ. -/
theorem model_facts (P : Params) (hS : P.Standing) (μ : ℝ) (hμ : μ ∈ P.rates) :
    (∀ i : ℕ, i < critAge P μ → p P i μ = 1) ∧
    (∀ i : ℕ, critAge P μ ≤ i → 1 ≤ i → p P i μ < p P (i - 1) μ) ∧
    (∀ μ' ∈ P.rates, μ ≤ μ' → critAge P μ' ≤ critAge P μ) := by sorry

end BleedFeed.ControlLimit
