-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_theorem_2
-- name    : EvolvHier.SocialOpt.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:27.047385+00:00
-- url     : https://prove2.me/theorems/e661ecb0-e0cb-4568-8e4b-164409132bf4
-- title:
--   Theorem 2 — unique decentralized socially optimal allocation scheme
-- statement:
--   Let $p$ satisfy all technology assumptions of §2. The allocation scheme $t^*$ transfers the whole unit revenue of agent $i\geq1$ to agent $i-1$, while agent 0 keeps her initial unit. Then $t^*$ is decentralized socially optimal, and every decentralized socially optimal scheme equals it:
--
--   $$t^*_{ij}=1\quad\Longleftrightarrow\quad (i=j+1)\text{ or }(i=j=0),\qquad t^*_{ij}=0\text{ otherwise}.$$
--
--   The scheme supports the constant equilibrium with $p'(\chi)=1$. The result identifies the transfer rule that maximizes attainable social value among all schemes and their Nash equilibria.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), Theorem 2, p. 12

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Theorem 2: the unique decentralized socially optimal allocation scheme. -/
theorem theorem_2 (T : Technology) :
    IsDecSociallyOptimal T tStar ∧
      ∀ t, IsScheme t → IsDecSociallyOptimal T t → t = tStar := by sorry

end EvolvHier.SocialOpt
