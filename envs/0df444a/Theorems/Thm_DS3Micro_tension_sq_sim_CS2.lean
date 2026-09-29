-- Prove2me | Theorems.Thm_DS3Micro_tension_sq_sim_CS2
-- name    : DS3Micro.tension_sq_sim_CS2
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:38:30.149794+00:00
-- url     : https://prove2.me/theorems/2b30697c-bbab-478c-a8ff-981e3cbc385c
-- title:
--   $(\widehat T^{(b)}_{1,1})^2 \sim C^{(b)}_{S^2}$: the ZZ tension squared matches the sphere normalization up to a $b$-independent constant
-- statement:
--   There is a nonzero complex constant $c$ such that for every $b\in\mathbb{C}$ with $b^2 = i\beta$ for some $\beta>0$,
--   $$C^{(b)}_{S^2} = c\,\big(\widehat T^{(b)}_{1,1}\big)^2,$$
--   where $C^{(b)}_{S^2} = 32\pi^4\Big(\frac{\sin(\pi b^2)\sin(\pi b^{-2})}{b^2-b^{-2}}\Big)^2$ is the sphere normalization (4.4) and $\widehat T^{(b)}_{1,1} = \frac{8b^2\sin(\pi b^2)\sin(\pi b^{-2})}{1-b^4}$ the reduced tension (4.34). This is condition (4.36), where $\sim$ means equality up to a $b$-independent factor.
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; eq. (4.36), p. 37, with (4.4) p. 27 and (4.34) p. 37.

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem tension_sq_sim_CS2 :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ b : ℂ, InRegime b → CS2 b = c * tensionHat b ^ 2 := by
  sorry
end DS3Micro
