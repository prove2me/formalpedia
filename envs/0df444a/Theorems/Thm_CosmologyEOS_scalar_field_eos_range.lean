-- Prove2me | Theorems.Thm_CosmologyEOS_scalar_field_eos_range
-- name    : CosmologyEOS.scalar_field_eos_range
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:38:49.980988+00:00
-- url     : https://prove2.me/theorems/ac2f8d84-7a58-4d32-b656-32dab0f053e8
-- title:
--   Scalar field: every $w\in[-1,1]$ is achievable, without crossing $w=-1$
-- statement:
--   Let $w(\dot\phi,V) = \dfrac{\frac12\dot\phi^2 - V}{\frac12\dot\phi^2 + V}$ be the scalar-field equation of state. Then:
--
--   1. (phantom divide) whenever the energy density $\frac12\dot\phi^2+V$ is positive, $w \ge -1$;
--   2. whenever additionally $V\ge 0$, $w\le 1$;
--   3. every value $w\in[-1,1]$ is achieved by some $\dot\phi$ and $V\ge 0$ with $\frac12\dot\phi^2+V>0$.
--
--   This is the source's statement that any equation of state between the free-field value $1$ and the cosmological-constant value $-1$, but not crossing the $w=-1$ barrier (the Phantom Divide Line), is achievable by a scalar field.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Scalar modeling' (Phantom Divide Line)

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem scalar_field_eos_range :
    (∀ phiDot V : ℝ, 0 < phiDot ^ 2 / 2 + V → -1 ≤ scalarFieldEOS phiDot V) ∧
    (∀ phiDot V : ℝ, 0 ≤ V → 0 < phiDot ^ 2 / 2 + V → scalarFieldEOS phiDot V ≤ 1) ∧
    (∀ w ∈ Set.Icc (-1 : ℝ) 1, ∃ phiDot V : ℝ,
      0 ≤ V ∧ 0 < phiDot ^ 2 / 2 + V ∧ scalarFieldEOS phiDot V = w) := by
  sorry

end CosmologyEOS
