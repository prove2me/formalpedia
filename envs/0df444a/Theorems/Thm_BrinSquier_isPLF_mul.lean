-- Prove2me | Theorems.Thm_BrinSquier_isPLF_mul
-- name    : BrinSquier.isPLF_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:09:59.237065+00:00
-- url     : https://prove2.me/theorems/5e9e6d6b-4047-41c8-b245-36483f373766
-- title:
--   Piecewise-linear homeomorphisms are closed under composition
-- statement:
--   If $f$ and $g$ are piecewise linear with finitely many breakpoints, so is $f\circ g$.
--
--   The statement asserts only that *some* finite breakpoint set works, not any particular one.
--
--   With the companion closure property for inverses, this is what makes $\mathrm{PLF}(\mathbb{R})$ a group rather than merely a set of maps. No `Subgroup` object is constructed by these two milestones; they supply the closure facts from which one can be built.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 488, Section 2: PLF(R) is a group under composition.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem isPLF_mul {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) : IsPLF (f * g) := by
  sorry

end BrinSquier
