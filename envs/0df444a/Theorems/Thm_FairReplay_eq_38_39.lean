-- Prove2me | Theorems.Thm_FairReplay_eq_38_39
-- name    : FairReplay.eq_38_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:20.824772+00:00
-- url     : https://prove2.me/theorems/89a1d856-0398-451b-8c1b-dce5c25c4980
-- title:
--   Eqs. (38)–(39) — the four-way differential $W$ vanishes under $H_0$ and equals $1$ iff $U\in(p+s,p+s+d]$ under $H_1$
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$, old thresholds $(p,p)$ at the edge $(u,v)$, and define the **pathwise differential** of a four-way replay round on the tape value $U$ by
--
--   $$
--   W=\bigl(P_1(u;U)-P_0(u;U)\bigr)-\bigl(P_1(v;U)-P_0(v;U)\bigr).
--   $$
--
--   Then:
--
--   1. under the null new thresholds $(p+s,p+s)$, $W=0$ for every $U\in[0,1]$;
--   2. under the alternative new thresholds $(p+s+d,p+s)$, for every $U\in[0,1]$,
--   $$
--   W=1\iff U\in(p+s,\,p+s+d];
--   $$
--   3. under the alternative, $\mathbb P(W=1)=d$ for $U\sim\mathrm{Unif}[0,1]$.
--
--   This is the statistic of the four-way test: a single observation $W=1$ is impossible under the null.
--
--   **Formalization Note** Outputs `true`/`false` are read as the integers $1$/$0$.
--
--   Differences from the source:
--   - encoding: outputs P_j(x;U) ∈ {0,1} and W an integer → Boolean outputs read as 0/1 in ℤ; reason: Lean convention; same values
--   - encoding: for every U, W = 0 almost surely, and probability d → for every U ∈ [0, 1], W = 0 (pointwise), and uniformTape-mass d of {W = 1}; reason: U ~ Unif[0, 1] takes its values in [0, 1], the support of the tape law; the pointwise identity is what the page proves ('identical for every U')
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), proof of Theorem 10.4, eqs. (38)–(39), pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_FairReplay_fourWayModel

open MeasureTheory

namespace FairReplay

/-- **Eqs. (38)–(39), the pathwise differential of four-way replay** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), proof of
Theorem 10.4, eqs. (38)–(39), pp.14–15 (PDF pp.16–17)): "Under four-way replay, define the
pathwise differential W = (P1(u; U) − P0(u; U)) − (P1(v; U) − P0(v; U)). Under H0, the two endpoint
deltas are identical for every U, so W = 0 almost surely. Under H1, W = 1 ⟺ U ∈ (p + s, p + s + d],
which occurs with probability d."

With old thresholds `(p, p)`, `W(new, U)` is the differential computed from the four-way outputs
`fourWayObs ![p, p] new U = (P0(u;U), P1(u;U), P0(v;U), P1(v;U))`, outputs read as `0/1` integers.
Under the null new thresholds `(p + s, p + s)` it vanishes for every tape value `U ∈ [0, 1]`; under
the alternative `(p + s + d, p + s)` it equals `1` exactly when `U ∈ (p + s, p + s + d]`, an event of
uniform-tape probability `d`.

**Formalization Note** Outputs `true/false` are read as `1/0` in `ℤ`. The endpoint `u` is index `0`
of the threshold vectors. -/
theorem eq_38_39 (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p + s + d < 1) :
    let b : Bool → ℤ := fun x => if x then 1 else 0
    let W : (Fin 2 → ℝ) → ℝ → ℤ := fun new U =>
      (b (fourWayObs ![p, p] new U 1) - b (fourWayObs ![p, p] new U 0)) -
        (b (fourWayObs ![p, p] new U 3) - b (fourWayObs ![p, p] new U 2))
    (∀ U ∈ Set.Icc (0 : ℝ) 1, W ![p + s, p + s] U = 0) ∧
      (∀ U ∈ Set.Icc (0 : ℝ) 1, W ![p + s + d, p + s] U = 1 ↔ U ∈ Set.Ioc (p + s) (p + s + d)) ∧
      uniformTape {U | W ![p + s + d, p + s] U = 1} = ENNReal.ofReal d := by sorry

end FairReplay
