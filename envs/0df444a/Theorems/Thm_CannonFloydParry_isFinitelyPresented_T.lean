-- Prove2me | Theorems.Thm_CannonFloydParry_isFinitelyPresented_T
-- name    : CannonFloydParry.isFinitelyPresented_T
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T09:33:58.79799+00:00
-- url     : https://prove2.me/theorems/77c0d3c5-d4b6-4146-9e5f-637204d70dc5
-- title:
--   Cannon–Floyd–Parry, p. 215 — Thompson's group $T$ is finitely presented
-- statement:
--   Thompson's group $T$, the group of piecewise linear homeomorphisms of the circle with dyadic
--   breakpoints, dyadic values at dyadic points and slopes powers of $2$, is finitely presented in
--   Mathlib's sense (`Group.IsFinitelyPresented`): it is finitely generated, and the kernel of some
--   surjection from a free group of finite rank onto it is the normal closure of finitely many
--   elements. No specific presentation is named in the statement.
--
--   **Source.** Cannon–Floyd–Parry, p. 215: “In unpublished notes [T1], Thompson proved that $T$ and
--   $V$ are finitely-presented, infinite simple groups.” This is the finite-presentation half for $T$;
--   its simplicity is `CannonFloydParry.isSimpleGroup_T`. In the notes it follows from Corollary 5.9,
--   $T_1 \cong T$, where $T_1$ has three generators and six relators (p. 236).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, p. 215, the introduction (a consequence of Corollary 5.9, T₁ ≅ T)

import Definitions.Def_CannonFloydParry_T
import Mathlib

namespace CannonFloydParry

theorem isFinitelyPresented_T : Group.IsFinitelyPresented T := by
  sorry

end CannonFloydParry
