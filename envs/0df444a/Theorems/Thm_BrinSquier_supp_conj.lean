-- Prove2me | Theorems.Thm_BrinSquier_supp_conj
-- name    : BrinSquier.supp_conj
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:02:25.413528+00:00
-- url     : https://prove2.me/theorems/f880d82a-39b7-4d68-9067-06f51608b4c1
-- title:
--   Conjugation carries supports along
-- statement:
--   For orientation-preserving homeomorphisms $f,g$ of $\mathbb{R}$,
--
--   $$\operatorname{supp}\bigl(f g f^{-1}\bigr) \;=\; f\bigl(\operatorname{supp} g\bigr).$$
--
--   A point is moved by the conjugate exactly when its preimage under $f$ is moved by $g$. No piecewise-linear hypothesis is needed — this holds for arbitrary bijections; continuity plays no role.
--
--   **Formalization note.** The source writes maps on the right and composes left to right, so its formula reads $\operatorname{supp}(f^{-1}gf) = (\operatorname{supp} g)f$. In Mathlib's convention $(f * g)\,x = f(g(x))$, which is why the conjugation appears on the other side here. The two say the same thing.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 487, observation (1.1a).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem supp_conj (f g : ℝ ≃o ℝ) : supp (f * g * f⁻¹) = f '' supp g := by
  sorry

end BrinSquier
