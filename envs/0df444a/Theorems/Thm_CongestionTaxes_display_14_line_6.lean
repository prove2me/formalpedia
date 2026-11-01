-- Prove2me | Theorems.Thm_CongestionTaxes_display_14_line_6
-- name    : CongestionTaxes.display_14_line_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:23.618922+00:00
-- url     : https://prove2.me/theorems/9e3ea10f-7da1-4a13-9060-97418a847720
-- title:
--   Display (14), line 6, p.20 — $p(x)\le\rho\,x\ell(x)$ at integer loads
-- statement:
--   Let every cost in $\mathcal L$ satisfy Assumption 1 and let $\rho=\sup_{\ell\in\mathcal L}\rho_\ell<\infty$. Then for every $\ell\in\mathcal L$ and every $x\in\mathbb N_0$,
--
--   $$
--   p(x)\ \le\ \rho\,x\,\ell(x).
--   $$
--
--   At $x=0$ both sides vanish; for $x\ge1$ this is the definition of $\rho_\ell\le\rho$. It is applied at the integer loads $v^{\mathrm{opt}}_r=|a^{\mathrm{opt}}|_r$.
--
--   Differences from the source:
--
--   - generalization: at $v^{\mathrm{opt}}_r=|a^{\mathrm{opt}}|_r$ → at every $x\in\mathbb N_0$, for every $\ell\in\mathcal L$; reason: the loads are nonnegative integers
--   - encoding: $\rho=\sup_{\ell}\rho_\ell$ (finite) → the real number $(\sup_\ell\rho_\ell)$ converted from $[0,\infty]$ under the hypothesis that it is finite; reason: same value
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (14), line 6, proof of Theorem 3, p.20

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_rhoSup

open scoped ENNReal

namespace CongestionTaxes

/-- Display (14), line 6 (Paccagnan, Gairing, arXiv:2105.07480v2, proof of Theorem 3, p.20, "by
def. of ρ, it is p_r(v_r^opt) ≤ ρ c_r(v_r^opt)"). Let every cost in `𝓛` satisfy Assumption 1 and
`ρ = sup_{ℓ∈𝓛} ρ_ℓ < ∞`. Then for every `ℓ ∈ 𝓛` and every integer load `x ∈ ℕ₀`,
`p(x) ≤ ρ · x ℓ(x)`.

**Formalization Note** `ρ` enters as the real number `(rhoSup L).toReal`, which is `sup ρ_ℓ` since
it is finite. The inequality is stated at integers only (`v^opt_r = |a^opt|_r` is a load); at
`x = 0` both sides are `0`. -/
theorem display_14_line_6 (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤)
    (ℓ : ℕ → ℝ) (hmem : ℓ ∈ L) (x : ℕ) :
    poissonValue ℓ (x : ℝ) ≤ (rhoSup L).toReal * ((x : ℝ) * ℓ x) := by sorry

end CongestionTaxes
