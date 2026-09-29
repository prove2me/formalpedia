-- Prove2me | Theorems.Thm_BrinSquier_isPLF_inv
-- name    : BrinSquier.isPLF_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:12:54.782982+00:00
-- url     : https://prove2.me/theorems/de751960-aad6-4411-b9b2-174e42718030
-- title:
--   Piecewise-linear homeomorphisms are closed under inverse
-- statement:
--   If $f$ is piecewise linear with finitely many breakpoints, so is $f^{-1}$. As with composition, only *some* finite breakpoint set is asserted.
--
--   Note that $f^{-1}$ is automatically an orientation-preserving homeomorphism — that comes from the type — so the only content here is the piecewise-linear condition.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 488, Section 2: PLF(R) is a group under composition.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem isPLF_inv {f : ℝ ≃o ℝ} (hf : IsPLF f) : IsPLF f⁻¹ := by
  sorry

end BrinSquier
