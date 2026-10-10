-- Prove2me | Theorems.Thm_CosmologyEOS_scalar_field_limiting_cases
-- name    : CosmologyEOS.scalar_field_limiting_cases
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:38:14.51677+00:00
-- url     : https://prove2.me/theorems/16f7dcaa-0794-4449-9f07-9744e377b438
-- title:
--   Scalar field: free field $w=1$, frozen field $w=-1$
-- statement:
--   For a homogeneous scalar field with time derivative $\dot\phi$ and potential energy $V$, the equation of state is $w = \dfrac{\frac12\dot\phi^2 - V}{\frac12\dot\phi^2 + V}$. Then:
--
--   1. a free field ($V = 0$) with $\dot\phi\neq 0$ has $w = 1$;
--   2. a field with vanishing kinetic energy ($\dot\phi = 0$) and $V\neq 0$ has $w=-1$, i.e. it is equivalent to a cosmological constant.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Scalar modeling'

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem scalar_field_limiting_cases :
    (∀ phiDot : ℝ, phiDot ≠ 0 → scalarFieldEOS phiDot 0 = 1) ∧
    (∀ V : ℝ, V ≠ 0 → scalarFieldEOS 0 V = -1) := by
  sorry

end CosmologyEOS
