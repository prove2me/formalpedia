-- Prove2me | Theorems.Thm_BrinSquier_commutator_id_near_common_fixed
-- name    : BrinSquier.commutator_id_near_common_fixed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:17:49.145753+00:00
-- url     : https://prove2.me/theorems/912bad1a-3768-4c45-9912-89a59d37cc45
-- title:
--   A commutator is the identity near a common fixed point
-- statement:
--   If piecewise-linear $f$ and $g$ both fix a point $t$, then $fgf^{-1}g^{-1}$ is the identity on some open interval around $t$.
--
--   $$f(t)=t,\ g(t)=t \;\implies\; \exists\,\varepsilon>0:\ \bigl(f g f^{-1} g^{-1}\bigr)(y)=y \ \text{ for } |y-t|<\varepsilon.$$
--
--   **What this does not say.** The interval depends on $t$ — there is no uniform choice — and nothing is claimed about the commutator away from $t$. It *does* follow that $f$ and $g$ commute on a (possibly smaller) neighbourhood of $t$; the two statements are equivalent up to shrinking the interval around $t$. If $f$ and $g$ share no fixed point the statement simply does not apply.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493, observation (2.14c).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem commutator_id_near_common_fixed {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g)
    {t : ℝ} (htf : f t = t) (htg : g t = t) :
    ∃ ε > 0, ∀ y ∈ Set.Ioo (t - ε) (t + ε), (f * g * f⁻¹ * g⁻¹) y = y := by
  sorry

end BrinSquier
