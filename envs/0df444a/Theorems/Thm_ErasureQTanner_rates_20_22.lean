-- Prove2me | Theorems.Thm_ErasureQTanner_rates_20_22
-- name    : ErasureQTanner.rates_20_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:13.257061+00:00
-- url     : https://prove2.me/theorems/ae6b627b-cc20-477f-b17a-1d8dd897810b
-- title:
--   (20)–(22) — the rates of §10.2
-- statement:
--   Let $\rho\in(0,\frac12)$ and $\varepsilon\in(0,1-2\rho)$, with inner codes of rates
--   $$\mathrm{rate}(C_A)=1-\rho-\frac\varepsilon3,\quad\mathrm{rate}(C_B)=\frac{\rho+\varepsilon/6}{1-\rho-\varepsilon/3},\quad\mathrm{rate}(D_A)=1-\frac\varepsilon4,\quad\mathrm{rate}(D_B)=\frac\varepsilon4.$$
--   Then for $\Delta$ large enough,
--   $$\mathrm{rate}(\mathcal C)\ge1-2\rho-\varepsilon,\quad\mathrm{rate}(C_A\otimes C_B)\ge\rho+\frac\varepsilon{12},\quad\mathrm{rate}(C_A^\perp\otimes D_B^\perp)\ge\rho+\frac\varepsilon{12}.$$
--   These inequalities put the local checks above the capacity of Theorem 15 while keeping the global rate near capacity.
--
--   Differences from the source:
--   - reading: rates as exact values → dimensions within $1$ of rate$\cdot\Delta$, $\Delta$ above a threshold; reason: an exact rate does not exist at every $\Delta$; the slack of the inequalities absorbs the rounding
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), eqs. (20)–(22), pp.26–27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_HX

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **The rates of §10.2, (20)–(22).** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), pp.26–27: with `rate(C_A) = 1 − ρ − ε/3`, `rate(C_B) = (ρ + ε/6)/(1 − ρ − ε/3)`,
`rate(D_A) = 1 − ε/4`, `rate(D_B) = ε/4`, for any `ε ∈ (0, 1 − 2ρ)`, "`rate(C_{ρ,ε,∆,n}) ≥ 1 − 2ρ − ε` (20) but also
`rate(C_A ⊗ C_B) ≥ ρ + ε/12`, (21) `rate(C_A^⊥ ⊗ D_B^⊥) ≥ ρ + ε/12`. (22)"

**Formalization Note.** Dimensions are within `1` of `rate·∆`, for every `∆` above a threshold that absorbs the rounding. `k = N − r_X − r_Z` with `r_X`, `r_Z` the ranks. -/
theorem rates_20_22 (ρ ε : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε : ε ∈ Set.Ioo (0 : ℝ) (1 - 2 * ρ)) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ L : LocalCodes Δ,
      |(Module.finrank (ZMod 2) L.CA : ℝ) - (1 - ρ - ε / 3) * Δ| ≤ 1 →
      |(Module.finrank (ZMod 2) L.CB : ℝ) - (ρ + ε / 6) / (1 - ρ - ε / 3) * Δ| ≤ 1 →
      |(Module.finrank (ZMod 2) L.DA : ℝ) - (1 - ε / 4) * Δ| ≤ 1 →
      |(Module.finrank (ZMod 2) L.DB : ℝ) - ε / 4 * Δ| ≤ 1 →
      (∀ Γ : LRData Δ, (1 - 2 * ρ - ε) * Γ.N ≤ (Γ.N : ℝ) - (HX Γ L).rank - (HZ Γ L).rank) ∧
      ρ + ε / 12 ≤ (Module.finrank (ZMod 2) (tensorCode L.CA L.CB) : ℝ) / (Δ : ℝ) ^ 2 ∧
      ρ + ε / 12 ≤ (Module.finrank (ZMod 2) (tensorCode (codeDual L.CA) (codeDual L.DB)) : ℝ) / (Δ : ℝ) ^ 2 := by sorry

end ErasureQTanner
