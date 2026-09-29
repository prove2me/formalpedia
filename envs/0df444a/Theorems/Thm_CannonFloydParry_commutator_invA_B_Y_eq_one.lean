-- Prove2me | Theorems.Thm_CannonFloydParry_commutator_invA_B_Y_eq_one
-- name    : CannonFloydParry.commutator_invA_B_Y_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:42:12.335204+00:00
-- url     : https://prove2.me/theorems/3a00f17f-5049-4aac-903e-7d572f0fd17d
-- title:
--   Line (3.3): $[A^{-1}B, Y_m] = 1$ in $F_1$ for $m \ge 3$
-- statement:
--   In the presented group $F_1$, with $Y_0 = A$ and $Y_m = A^{-(m-1)} B A^{m-1}$ for
--   $m \ge 1$: for every $m \ge 3$,
--   $$(A^{-1}B)\, Y_m\, (A^{-1}B)^{-1}\, Y_m^{-1} = 1,$$
--   i.e. $A^{-1}B$ commutes with $Y_m$. This is the source's line (3.3), with its bracket
--   $[x, y] = x y x^{-1} y^{-1}$ written out.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, pp. 225–226, line (3.3)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Line (3.3), p. 225: in `F₁`, `[A⁻¹B, Yₘ] = 1` for `m ≥ 3`, with `[x, y] = x y x⁻¹ y⁻¹`. -/
theorem commutator_invA_B_Y_eq_one (m : ℕ) (hm : 3 ≤ m) :
    ((PresentedGroup.of FormalAB.A : F1)⁻¹ * PresentedGroup.of FormalAB.B) * Y m
      * ((PresentedGroup.of FormalAB.A : F1)⁻¹ * PresentedGroup.of FormalAB.B)⁻¹ * (Y m)⁻¹ = 1 := by
  sorry

end CannonFloydParry
