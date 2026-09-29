-- Prove2me | Theorems.Thm_Devaney_shift_continuous
-- name    : Devaney.shift_continuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:32:22.718168+00:00
-- url     : https://prove2.me/theorems/3347d64e-be63-45d7-a8cb-a9bb5f451369
-- title:
--   Proposition 6.5 — the shift map is continuous
-- statement:
--   The shift map $\sigma : \Sigma_2 \to \Sigma_2$, $\sigma(s_0 s_1 s_2 \dots) = (s_1 s_2 s_3 \dots)$, is continuous for the metric $d[s,t] = \sum_i |s_i - t_i| 2^{-i}$.
--
--   Continuity is what makes $\sigma$ a dynamical system rather than a mere set map, and it is needed before any conjugacy with $F_\mu$ can be claimed.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, p. 41, Proposition 6.5

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem shift_continuous : Continuous (shift : Sigma2 → Sigma2) := by sorry
end Devaney
