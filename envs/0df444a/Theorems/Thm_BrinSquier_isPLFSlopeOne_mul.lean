-- Prove2me | Theorems.Thm_BrinSquier_isPLFSlopeOne_mul
-- name    : BrinSquier.isPLFSlopeOne_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:03:06.745757+00:00
-- url     : https://prove2.me/theorems/49a8c14a-58f9-44a3-99b5-81656b02b0e3
-- title:
--   Slope one at both ends is closed under composition
-- statement:
--   If $f$ and $g$ are each piecewise linear with finitely many breakpoints and have slope $1$ near $-\infty$ and near $+\infty$, then so does $f \circ g$.
--
--   Slope $1$ at an end means the map agrees with a **translation** on a ray out to that end — not that it is the identity there, and the translation constants at the two ends are unrelated. Composing two translations near $-\infty$ gives a translation with the sum of the constants, and likewise at $+\infty$; the thresholds must be shrunk so that the inner map's image still lies in the outer map's window.
--
--   **Role.** With its companion for inverses, this is what makes the slope-one maps a *subgroup* of $\mathrm{PLF}(\mathbb{R})$ rather than merely a set. That is what carries Brin-Squier's (2.14a) — a single commutator has slope $1$ at both ends — to the statement that *every* element of the derived subgroup does, which is the form the main dichotomy (3.2) needs. The closure milestones for $\mathrm{IsPLF}$ supply the piecewise-linear half; this supplies the slope half.
--
--   **Formalization note.** No `Subgroup` object is constructed. The statement asserts only that some thresholds and translation constants work, not any particular ones.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493: the passage identifying the commutator subgroup PLF'(R) of PLF(R) with the elements of slope 1 near -oo and +oo presupposes that those elements form a subgroup. PROVENANCE: the closure property itself is not stated as a numbered result in the paper, which treats it as immediate; it is recorded here because it is the step from (2.14a), p. 493, to the hypothesis of Theorem (3.2), p. 494.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem isPLFSlopeOne_mul {f g : ℝ ≃o ℝ} (hf : IsPLFSlopeOne f) (hg : IsPLFSlopeOne g) :
    IsPLFSlopeOne (f * g) := by
  sorry

end BrinSquier
