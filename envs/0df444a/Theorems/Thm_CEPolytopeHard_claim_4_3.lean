-- Prove2me | Theorems.Thm_CEPolytopeHard_claim_4_3
-- name    : CEPolytopeHard.claim_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:51.449+00:00
-- url     : https://prove2.me/theorems/dcf39cfe-b9e8-47ed-afb8-3fb71c7dbbc2
-- title:
--   Claim 4.3 — the minimum feasible $t$ in (13) is $p_m(x)$
-- statement:
--   For every $m \in \mathbb N$ and every $x \in [0,1]$, the least $t$ such that $(x, t, w_1, \dots, w_m)$ lies in the polytope (13) for some $w$ is $p_m(x)$:
--   $$
--   p_m(x) = \min\{t : \exists w,\ (x, t, w) \in (13)\},
--   $$
--   and the minimum is attained at $w_j = T^{(j)}(x)$, $j = 1, \dots, m$.
--
--   In the constructed game a player pays $t$ linearly, so it chooses the minimal lift, whose cost $p_m(x)$ approximates $x^2$.
--
--   Differences from the source:
--   - generalization: a fixed m (the least positive m of (18)) → every m ∈ ℕ, including m = 0; reason: the claim holds for every m and specializes to the paper's
--   - encoding: variables (x, t, w_1, …, w_m) with w_0 = x → w : Fin (m + 1) → ℝ listing w_0, …, w_m with the constraint w_0 = x; T^{(0)}(x) = x; reason: same polytope
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Claim 4.3, p.22

import Mathlib
import Definitions.Def_CEPolytopeHard_pm

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Claim 4.3 (the lift recovers `p_m`)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Claim 4.3, p.22: "For every fixed x ∈ [0, 1], the
minimum feasible t in (13) is p_m(x), attained when w_j = T^{(j)}(x)").

For every `m ∈ ℕ` and `x ∈ [0, 1]`, `p_m(x)` is the least `t` for which some `w` makes
`(x, t, w)` a point of the polytope (13), and `(x, p_m(x), (T^{(j)}(x))_{j=0}^{m})` is such a point.

**Formalization Note** `w` lists `w_0 = x, w_1, …, w_m` (`InPoly13`); `T^{(0)}(x) = x`. The paper
uses the claim with the least positive `m` of (18); it is stated here for every `m`, including
`m = 0` (polytope `0 ≤ x, t ≤ 1`, `t ≥ x`). -/
theorem claim_4_3 (m : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsLeast {t : ℝ | ∃ w : Fin (m + 1) → ℝ, InPoly13 m x t w} (pm m x) ∧
    InPoly13 m x (pm m x) (fun j => tent^[j.val] x) := by sorry

end CEPolytopeHard
