-- Prove2me | Theorems.Thm_BrinSquier_compact_closure_supp_commutator
-- name    : BrinSquier.compact_closure_supp_commutator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:17:22.449731+00:00
-- url     : https://prove2.me/theorems/a6110674-ba3e-442e-b9d1-da10f2b1abbd
-- title:
--   A commutator of two homeomorphisms with slope one at both ends has bounded support
-- statement:
--   If $f$ and $g$ each have slope $1$ near $-\infty$ and near $+\infty$, then the support of the commutator $fgf^{-1}g^{-1}$ has **compact closure** — equivalently, the commutator is the identity outside a bounded set.
--
--   $$\overline{\operatorname{supp}\bigl(f g f^{-1} g^{-1}\bigr)} \text{ is compact.}$$
--
--   **Why the hypothesis is on the commutator and not on a single map.** Slope $1$ at both ends does *not* make a map's own support bounded: the translation $y \mapsto y+1$ has slope $1$ at both ends and support all of $\mathbb{R}$. It is exactly the commutator that kills the translation constants the two maps have near each end. **The slope hypotheses are sufficient but not necessary.** They cannot simply be dropped: for $f(y)=2y$ and $g(y)=y+1$ the commutator is $y \mapsto y+1$, whose support is unbounded. They are not *necessary* for the conclusion, though — $f(y)=2y$ and $g(y)=4y$ have slope $\neq 1$ at both ends and commute, so their commutator has empty support.
--
--   **Deviation from the source.** Brin and Squier state (2.14b) for elements of $\mathrm{PLF}(\mathbb{R})$. The piecewise-linear hypothesis is not used — only the behaviour at the two ends — so it is omitted here and the statement holds for arbitrary orientation-preserving homeomorphisms.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493, observation (2.14b). Stated there for f, g in PLF(R); the piecewise-linear hypothesis is unused and is dropped here.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem compact_closure_supp_commutator {f g : ℝ ≃o ℝ}
    (hfb : SlopeAtBot f 1) (hft : SlopeAtTop f 1)
    (hgb : SlopeAtBot g 1) (hgt : SlopeAtTop g 1) :
    IsCompact (closure (supp (f * g * f⁻¹ * g⁻¹))) := by
  sorry

end BrinSquier
