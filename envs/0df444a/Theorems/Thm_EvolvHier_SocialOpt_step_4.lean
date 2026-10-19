-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_4
-- name    : EvolvHier.SocialOpt.step_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:35.613257+00:00
-- url     : https://prove2.me/theorems/98954ef6-b141-48f4-8f8b-d626fd83bc7f
-- title:
--   Step 4 — the full-transfer scheme is socially optimal
-- statement:
--   The scheme $t^*$ that transfers the full unit revenue of each arriving successor to its immediate predecessor is decentralized socially optimal. It has an equilibrium whose social value is at least that of every equilibrium of every valid allocation scheme:
--
--   $$\exists x\in\operatorname{Eq}(t^*):\quad V(y)\leq V(x)\quad\text{for all valid }t\text{ and }y\in\operatorname{Eq}(t).$$
--
--   This establishes the existence half of Theorem 2.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 4, p. 26

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 4. -/
theorem step_4 (T : Technology) : IsDecSociallyOptimal T tStar := by sorry

end EvolvHier.SocialOpt
