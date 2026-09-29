-- Prove2me | Theorems.Thm_FamousTheorems_machin_formula
-- name    : FamousTheorems.machin_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:11.369747+00:00
-- url     : https://prove2.me/theorems/fc8759b5-f1ca-4c1d-82b8-0b76b164b1dc
-- title:
--   Machin's formula for π
-- statement:
--   **Machin's formula.**
--   $$4\arctan\frac15-\arctan\frac1{239}=\frac\pi4.$$
--
--   John Machin found this identity in 1706 and used it to compute $100$ decimal digits of $\pi$. Because the arctangent series converge quickly at $1/5$ and $1/239$, Machin-like formulas remained the main method of computing $\pi$ until the late twentieth century.
--
--   **Formalization note.** Mathlib's `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`, with `Real.arctan` the real arctangent.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem machin_formula : 4 * Real.arctan 5⁻¹ - Real.arctan 239⁻¹ = Real.pi / 4 := by sorry

end FamousTheorems
