-- Prove2me | Theorems.Thm_ContinuityEqWiki_div_curl_eq_zero
-- name    : ContinuityEqWiki.div_curl_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:27.373135+00:00
-- url     : https://prove2.me/theorems/3652b5b8-a6b1-4447-9462-9e3ca0b75790
-- title:
--   The divergence of a curl vanishes: $\nabla\cdot(\nabla\times F)=0$
-- statement:
--   Let $F:\mathbb R^3\to\mathbb R^3$ be a vector field of class $C^2$. Then for every $x\in\mathbb R^3$,
--   $$\nabla\cdot(\nabla\times F)(x)=0.$$
--
--   The source uses this identity when it takes the divergence of Ampère's law to derive charge conservation from Maxwell's equations.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Electromagnetism", box "Consistency with Maxwell's equations" ("but the divergence of a curl is zero")

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem div_curl_eq_zero (F : Space → Space) (hF : ContDiff ℝ 2 F) (x : Space) :
    div (curl F) x = 0 := by sorry

end ContinuityEqWiki
