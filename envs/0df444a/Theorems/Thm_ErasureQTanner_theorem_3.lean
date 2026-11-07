-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_3
-- name    : ErasureQTanner.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:25.45229+00:00
-- url     : https://prove2.me/theorems/fea79584-ce8c-446e-8aec-0482f9ce7ae4
-- title:
--   Theorem 3 — linear distance, four-code form
-- statement:
--   Let $\delta,\kappa>0$. For $\Delta$ large enough, every quantum Tanner code on a Ramanujan left-right Cayley complex, with inner codes of distance at least $\delta\Delta$ and robustness $\kappa$, has
--   $$d_{\min}\ge\frac{\delta^2\kappa^2}{256\Delta}N.$$
--   The paper notes that [LZ23] proved this for $D_A=C_A$, $D_B=C_B$ and that the proof extends verbatim.
--
--   Differences from the source:
--   - reading: "Ramanujan" → non-bipartite Ramanujan on both sides; reason: the setting of [LZ23]; the complexes the proof uses have it
--   - reading: robustness of "the four tensor codes on Figure 3" → robustness of the eight pairs of `GoodLocal`; reason: the conventions of p.7 and p.20 name different pairs, and §10.1 uses both
--   - encoding: $d_{\min}=\min(d_X,d_Z)$ → the two bounds on words of $C_Z\setminus C_X^\perp$ and $C_X\setminus C_Z^\perp$; reason: a zero logical space gives no junk value
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 3, p.8

import Mathlib
import Definitions.Def_ErasureQTanner_HX

set_option autoImplicit false

namespace ErasureQTanner

/-- **Theorem 3** ([LZ23]). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.8: "For a constant `∆` large enough, the quantum Tanner codes described in the construction above
with a Ramanujan left-right Cayley complex have a linear minimum distance: `d_min ≥ (δ²κ²/(256∆))N`."

**Formalization Note.** `d = min(d_X, d_Z)` (§2, p.4) is stated by its two defining bounds, so a zero logical space gives no junk value.
`Δ₀` depends on `δ`, `κ` (p.26: "a sufficiently large `∆` should be chosen" after them). The hypotheses are `GoodLocal δ κ`
and non-bipartite Ramanujan. The constant `1/256` is as printed. -/
theorem theorem_3 (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ L : LocalCodes Δ, GoodLocal δ κ L.CA L.CB L.DA L.DB →
    ∀ Γ : LRData Δ, Γ.IsRamanujan →
      (∀ w ∈ checkKer (HZ Γ L), w ∉ checkRows (HX Γ L) →
        δ ^ 2 * κ ^ 2 / (256 * Δ) * Γ.N ≤ (hammingNorm w : ℝ)) ∧
      (∀ w ∈ checkKer (HX Γ L), w ∉ checkRows (HZ Γ L) →
        δ ^ 2 * κ ^ 2 / (256 * Δ) * Γ.N ≤ (hammingNorm w : ℝ)) := by sorry

end ErasureQTanner
