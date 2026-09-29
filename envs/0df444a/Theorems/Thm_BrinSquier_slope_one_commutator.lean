-- Prove2me | Theorems.Thm_BrinSquier_slope_one_commutator
-- name    : BrinSquier.slope_one_commutator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:16:57.560547+00:00
-- url     : https://prove2.me/theorems/1aada959-aacd-4ba5-84e7-148025677a9a
-- title:
--   A commutator in PLF(ℝ) has slope one at both ends
-- statement:
--   For piecewise-linear $f,g$ with finitely many breakpoints, the commutator $fgf^{-1}g^{-1}$ has slope $1$ near $-\infty$ and near $+\infty$.
--
--   **What this does not say.** It does *not* say the commutator is the identity near the ends. Slope $1$ at an end means a *translation* there, and the translation constant is generally nonzero. Being the identity near both ends is a strictly stronger property, and it is what (2.14b) extracts from two maps that already have slope $1$ at both ends.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493, observation (2.14a).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem slope_one_commutator {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) :
    SlopeAtBot (f * g * f⁻¹ * g⁻¹) 1 ∧ SlopeAtTop (f * g * f⁻¹ * g⁻¹) 1 := by
  sorry

end BrinSquier
