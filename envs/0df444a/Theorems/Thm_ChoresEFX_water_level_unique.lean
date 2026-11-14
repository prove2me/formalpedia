-- Prove2me | Theorems.Thm_ChoresEFX_water_level_unique
-- name    : ChoresEFX.water_level_unique
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:05:37.309835+00:00
-- url     : https://prove2.me/theorems/5df9c767-0f23-43a0-883d-d20d2e1efe31
-- title:
--   Eq. (2) — the water level exists and is unique when $m\beta>n$
-- statement:
--   Let $n\ge1$, $\beta>0$, let $r$ be a positive vector indexed by $m$ chores, and suppose $m\beta>n$. Then the equation
--
--   $$\sum_g\min\{s\,r_g,\beta\}=n$$
--
--   has a unique solution $s>0$.
--
--   This makes the prices of each round of MFCP well defined.
--
--   Differences from the source:
--   - generalization: r is the base price vector r(v) of a round, and n ≥ 2 → any positive vector r, and n ≥ 1; reason: base prices are positive, so the page's case is a special case; the argument uses nothing more
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §3.1, the sentence after Eq. (2), p.7

import Mathlib

namespace ChoresEFX

/-- **The water level exists and is unique**, §3.1, p.7, the sentence after Eq. (2).

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

If `mβ > n`, the equation `∑_g min{s · r_g, β} = n` has a unique solution `s > 0`.

**Formalization Note.** `r` is any positive vector, in particular the base prices `r_g(v)` of a round;
`n > 0` is the paper's standing `n ≥ 2` weakened as far as the sentence needs. -/
theorem water_level_unique {κ : Type*} [Fintype κ] (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 < β)
    (r : κ → ℝ) (hr : ∀ g, 0 < r g) (hmβ : (n : ℝ) < (Fintype.card κ : ℝ) * β) :
    ∃! s : ℝ, 0 < s ∧ ∑ g, min (s * r g) β = (n : ℝ) := by sorry

end ChoresEFX
