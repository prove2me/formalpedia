-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_5
-- name    : EvolvHier.SocialOpt.step_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:22.001981+00:00
-- url     : https://prove2.me/theorems/4f050980-38d7-4354-b5e9-98e5ad8be5e0
-- title:
--   Step 5 — uniqueness of the socially optimal scheme
-- statement:
--   Every decentralized socially optimal allocation scheme is exactly the full-transfer scheme $t^*$:
--
--   $$t\text{ is decentralized socially optimal}\quad\Longrightarrow\quad t=t^*.$$
--
--   Equality here is equality of every transfer entry, not merely equality of supported equilibria or social values. This is the uniqueness half of Theorem 2.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 5, pp. 26–27

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 5. -/
theorem step_5 (T : Technology) :
    ∀ t, IsScheme t → IsDecSociallyOptimal T t → t = tStar := by sorry

end EvolvHier.SocialOpt
