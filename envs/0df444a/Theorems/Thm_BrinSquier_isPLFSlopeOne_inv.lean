-- Prove2me | Theorems.Thm_BrinSquier_isPLFSlopeOne_inv
-- name    : BrinSquier.isPLFSlopeOne_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:03:10.906995+00:00
-- url     : https://prove2.me/theorems/0e758320-0701-4ecb-b936-a27bb571850c
-- title:
--   Slope one at both ends is closed under inverse
-- statement:
--   If $f$ is piecewise linear with finitely many breakpoints and has slope $1$ near $-\infty$ and near $+\infty$, then so does $f^{-1}$.
--
--   Slope $1$ at an end means $f(y) = y + b$ on a ray out to that end, for some unconstrained constant $b$. Inverting gives $f^{-1}(w) = w - b$, valid on the shifted ray; the two ends are handled separately and their constants need not agree.
--
--   **Role.** The companion to the closure property for composition. Together they make the slope-one maps a subgroup of $\mathrm{PLF}(\mathbb{R})$, which is what lets Brin-Squier's (2.14a) — a single commutator has slope $1$ at both ends — be promoted to every element of the derived subgroup, as the main dichotomy (3.2) requires.
--
--   **Formalization note.** `f⁻¹` is the inverse order isomorphism; no `Subgroup` object is built.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493, same passage as the companion composition property. PROVENANCE: not a numbered result in the paper, which treats the subgroup property of the slope-one set as immediate; recorded here as the other half of the step from (2.14a) to the hypothesis of (3.2).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem isPLFSlopeOne_inv {f : ℝ ≃o ℝ} (hf : IsPLFSlopeOne f) :
    IsPLFSlopeOne f⁻¹ := by
  sorry

end BrinSquier
