-- Prove2me | Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_range_eq_ker
-- name    : BraidsLinksMCG.fadellNeuwirth_range_eq_ker
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:17:23.13846+00:00
-- url     : https://prove2.me/theorems/df71e468-aabf-4e86-9f5b-18e3cb66778b
-- title:
--   Exactness at the middle of the Fadell--Neuwirth sequence
-- statement:
--   Exactness at the middle term of the Fadell–Neuwirth sequence: in
--
--   $$\pi_1igl(E^{2}-Q_nigr) \longrightarrow \pi_1igl(F_{0,n+1}E^{2}igr) \longrightarrow \pi_1igl(F_{0,n}E^{2}igr),$$
--
--   the image of the map induced by the fibre inclusion `configIncl` equals the kernel of the map induced by the forgetful map `configForget`.
--
--   In words: a pure braid on $n+1$ strands becomes trivial after forgetting the last strand exactly when it comes from a loop of that last strand alone in the plane punctured at the other $n$ points. One inclusion is the easy one --- forgetting the last strand of a braid that only moves the last strand gives the trivial braid --- and the other is the substance, requiring the homotopy lifting property of the fibration to push a null-homotopy of the forgotten braid back up to the total space.
--
--   This is one of the three conjuncts of `BraidsLinksMCG.thm_1_4_fadell_neuwirth_exact`, separated out so that it can be cited on its own. Together with injectivity of the first map and surjectivity of the second --- the latter being a formal consequence of the existence of a section --- it gives the short exact sequence
--
--   $$1 	o F_n 	o P_{n+1} 	o P_n 	o 1$$
--
--   that underlies the combing of pure braids.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4; Fadell and Neuwirth, Configuration spaces, Math. Scand. 10 (1962).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem fadellNeuwirth_range_eq_ker (n : ℕ) :
    (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range =
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker := by sorry

end BraidsLinksMCG
