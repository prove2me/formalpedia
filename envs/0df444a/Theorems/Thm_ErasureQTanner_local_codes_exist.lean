-- Prove2me | Theorems.Thm_ErasureQTanner_local_codes_exist
-- name    : ErasureQTanner.local_codes_exist
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:01.393588+00:00
-- url     : https://prove2.me/theorems/b57c26dd-4df2-4627-805b-b5420826add5
-- title:
--   §4, p.7 — random inner codes satisfy all the requirements
-- statement:
--   For rates $r_1,\dots,r_4\in(0,1)$ there are $\delta,\kappa>0$, depending only on the rates, such that independent uniform random $C_A,C_B,D_A,D_B$ of these rates have, with probability tending to $1$ as $\Delta\to\infty$: minimum distance at least $\delta\Delta$ for the four codes and their duals, and robustness $\kappa$ for the eight pairs of the requirement `GoodLocal`.
--
--   Differences from the source:
--   - reading: "all these requirements", "the four tensor codes on Figure 3" → the eight robustness pairs of `GoodLocal`; reason: the conventions of p.7 and p.20 name different pairs, and §10.1 uses both
--   - reading: component codes of fixed rates → every dimension within $1$ of $r_i\Delta$; reason: an exact rate does not exist at every $\Delta$
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §4, p.7

import Mathlib
import Definitions.Def_ErasureQTanner_LocalCodes
import Definitions.Def_ErasureQTanner_uniformAvg

set_option autoImplicit false

namespace ErasureQTanner

/-- **The local codes exist** (§4, p.7, unnumbered). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.7: "When the rates of the inner component codes `C_A, C_B, D_A, D_B` are
fixed, one can satisfy all these requirements simultaneously, with probability tending to one as `∆ → ∞`, by choosing
independent uniform random linear component codes."

**Formalization Note.** "All these requirements" is `GoodLocal δ κ`: distance `≥ δ∆` for the four codes and their duals, and `κ`-robustness
for the eight pairs. `δ`, `κ` depend on the rates only. Dimensions are every `k_i` within `1` of `r_i∆`. "Tending to one" is the
`θ`-`Δ₀` form. -/
theorem local_codes_exist (r₁ r₂ r₃ r₄ : ℝ) (h₁ : r₁ ∈ Set.Ioo (0 : ℝ) 1) (h₂ : r₂ ∈ Set.Ioo (0 : ℝ) 1)
    (h₃ : r₃ ∈ Set.Ioo (0 : ℝ) 1) (h₄ : r₄ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ θ : ℝ, 0 < θ → ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ k₁ k₂ k₃ k₄ : ℕ,
      |(k₁ : ℝ) - r₁ * Δ| ≤ 1 → |(k₂ : ℝ) - r₂ * Δ| ≤ 1 →
      |(k₃ : ℝ) - r₃ * Δ| ≤ 1 → |(k₄ : ℝ) - r₄ * Δ| ≤ 1 →
      1 - θ ≤ uniformAvg Δ k₁ (fun CA => uniformAvg Δ k₂ fun CB => uniformAvg Δ k₃ fun DA =>
        uniformProb Δ k₄ fun DB => GoodLocal δ κ CA CB DA DB) := by sorry

end ErasureQTanner
