-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_tstar_equilibrium
-- name    : EvolvHier.SocialOpt.tstar_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:21.716492+00:00
-- url     : https://prove2.me/theorems/c44d9f2b-eaac-4a43-8bca-2e2307b63f8f
-- title:
--   Step 4 and Proposition 1 — the constant equilibrium of the full-transfer scheme
-- statement:
--   The full-transfer scheme $t^*$ has a constant equilibrium $x_i=\chi>0$ satisfying the marginal condition $p'(\chi)=1$. Every equilibrium of this scheme equals this constant profile:
--
--   $$\exists\chi>0:\quad p'(\chi)=1,\quad x=(\chi,\chi,\ldots)\text{ is the unique equilibrium of }t^*.$$
--
--   This identifies the equilibrium that supports the scheme in Theorem 2.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 4, p. 26; proof of Proposition 1, p. 27

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- The constant equilibrium used in Theorem 2, Step 4. -/
theorem tstar_equilibrium (T : Technology) :
    ∃ χ : ℝ, 0 < χ ∧ deriv T.p χ = 1 ∧
      IsEquilibrium T tStar (fun _ => χ) ∧
      ∀ x, IsEquilibrium T tStar x → x = fun _ => χ := by sorry

end EvolvHier.SocialOpt
