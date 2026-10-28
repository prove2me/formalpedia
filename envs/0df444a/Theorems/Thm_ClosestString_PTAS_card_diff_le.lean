-- Prove2me | Theorems.Thm_ClosestString_PTAS_card_diff_le
-- name    : ClosestString.PTAS.card_diff_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:16.170183+00:00
-- url     : https://prove2.me/theorems/6046b78d-d7f3-4170-8f2c-265658407a5b
-- title:
--   Proof of Theorem 7 — |P| ≤ r·d_opt: an r-tuple disagrees on at most r·d_opt positions
-- statement:
--   Let $u_1,\dots,u_n$ be strings of one length, $c$ a string of that length and $d\ge0$ with $d(u_i,c)\le d$ for every $i$. For any indices $i_1,\dots,i_r$ (repetitions allowed) let $P=\{1,\dots,m\}\setminus Q_{i_1,\dots,i_r}$ be the positions where $u_{i_1},\dots,u_{i_r}$ do not all agree. Then
--
--   $$|P|\ \le\ r\,d.$$
--
--   At every position of $P$ at least one of the $r$ strings differs from the center. The bound is used in the proof of Theorem 9 (p. 11) to turn the additive error $\varepsilon|P|$ into $\varepsilon r\,d_{\mathrm{opt}}$.
--
--   Differences from the source:
--
--   - generalization: s an optimal center, d_opt its radius, an r-element subset of the strings → any center c, any radius bound d, any r-tuple of indices (repetitions allowed), any r ≥ 0; reason: the argument uses only d(u_i, c) ≤ d; the paper's subsets and Theorem 9's tuples (with u = t) are special cases
--   - encoding: positions 1..m, indices 1..n, s_{i1} → 0-based Fin m, Fin n; s_{i1} is u (idx 0); reason: relabelling; changes no instance
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 7, proof of Theorem 7 (restated as "|P| ≤ r d_opt" in the proof of Theorem 9, p. 11)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

/-- **`|P| ≤ r × d_opt`** (proof of Theorem 7, Li, Ma & Wang, arXiv:cs/0002012v1, p. 7; used again
in the proof of Theorem 9, p. 11): for any strings `u_1, …, u_n` of one length, any center `c` with
`d(u_i, c) ≤ d` for all `i`, and any `r`-tuple of indices `idx`, the positions where
`u_{idx 0}, …, u_{idx (r-1)}` do not all agree number at most `r · d`. -/
theorem card_diff_le {A : Type*} [DecidableEq A] {n m : ℕ} (u : Fin n → Fin m → A)
    (c : Fin m → A) (d : ℕ) (hd : ∀ i, hammingDist (u i) c ≤ d) (r : ℕ) (idx : Fin r → Fin n) :
    (agreeSet u idx)ᶜ.card ≤ r * d := by sorry

end ClosestString.PTAS
