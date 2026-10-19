-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_0
-- name    : EvolvHier.SocialOpt.step_0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:26.713926+00:00
-- url     : https://prove2.me/theorems/6bbc2ba5-7c75-458c-88a1-8b1b46cff34c
-- title:
--   Step 0 — finite expected investment implies finite expected length
-- statement:
--   For every nonnegative investment profile $x$ under the paper's technology, finite expected investment entails finite expected hierarchy length:
--
--   $$I(x)<\infty\quad\Longrightarrow\quad L(x)<\infty.$$
--
--   This controls the infinite series used to compare social values and to define the attainable-length frontier.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 0, pp. 20–21

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 0: finite investment gives finite length. -/
theorem step_0 (T : Technology) (x : ℕ → ℝ) (hx : IsProfile x)
    (hI : I T x ≠ ⊤) : L T x ≠ ⊤ := by sorry

end EvolvHier.SocialOpt
