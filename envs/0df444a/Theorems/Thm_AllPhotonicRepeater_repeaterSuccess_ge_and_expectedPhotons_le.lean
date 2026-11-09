-- Prove2me | Theorems.Thm_AllPhotonicRepeater_repeaterSuccess_ge_and_expectedPhotons_le
-- name    : AllPhotonicRepeater.repeaterSuccess_ge_and_expectedPhotons_le
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:23:59.062572+00:00
-- url     : https://prove2.me/theorems/bff6246f-80e5-4ae3-be3f-7dc0599cd109
-- title:
--   Eqs. (C1), (C4): $P\ge1/8$ and $\bar Q\le 8\,(2mn(Q_L+1)+2m)$
-- statement:
--   Let $0\le\epsilon_0\le1$, let $n,m,l\in\mathbb N$ with $m\ge1$, let $b_0,\dots,b_l$ be branching parameters and let $\delta\in\mathbb R$. Suppose that
--
--   1. the loss-tolerant measurements fail with probability at most $\delta$: $1-P_Z\le\delta$ and $1-P_X\le\delta$;
--   2. $2mn\delta\le 1/2$;
--   3. the Bell factor of (C1) satisfies $[1-(1-P_B)^m]^{n+1}\ge 1/4$.
--
--   Then the success probability (C1) and the average photon number (C4) satisfy
--   $$
--   P\ge\frac18\qquad\text{and}\qquad \bar Q=\frac{2mn(Q_L+1)+2m}{P}\le 8\,\big(2mn(Q_L+1)+2m\big).
--   $$
--   This is the assembly step of the scaling argument: bounds on the three factors of (C1) give a bound on $\bar Q$ that is linear in $mn(Q_L+1)$.
--
--   Differences from the source:
--   - reading: (C1) and (C4) as formulas, combined with the upper bound $\bar Q_{upp}$ (C9), p. 12 → the inequality $P\ge1/8$, $\bar Q\le8(2mn(Q_L+1)+2m)$ under bounds on the factors of (C1); reason: the paper bounds $\bar Q$ through $P_L$ and (C9), which then needs the numerical (A4); this item bounds the factors of (C1) directly
--   - generalization: $\epsilon_0<0.5$ (standing assumption, p. 11) → $0\le\epsilon_0\le1$; reason: the assembly holds for every loss probability; it specializes to the paper's range
--   - reading: (A3) printed for $1\le k\le l$ → $R_k$ given by (A3) also at $k=0$; reason: (A16) reads $P_X=R_0$, and (A7), (A9), (A12) give $R_k=1-(1-S_k)^{b_k}$ at every level, $k=0$ included
--   - encoding: $R_{l+1}:=0$ and $b_{l+1}:=0$ → $R_k=0$ and $b_k$ read as $0$ for every $k>l$; reason: $R_{l+2}$ enters only $R_l$, raised to the power $b_{l+1}=0$, so its value never matters; same instances
--   - encoding: exponent $2(m-1)n$ → natural-number exponent `2 * (m - 1) * n` with truncated subtraction; reason: differs only at $m=0$, which the statement excludes ($m\ge1$)
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, Eqs. (C1), (C4), p. 11

import Mathlib
import Definitions.Def_AllPhotonicRepeater_expectedPhotons

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. C1, Eqs. (C1)
and (C4), p. 11: for `0 ≤ ε0 ≤ 1`, if `m ≥ 1`, the loss-tolerant measurements fail with
probability at most `δ` (`1 − P_Z ≤ δ`, `1 − P_X ≤ δ`), `2mnδ ≤ 1/2`, and the Bell factor
`[1 − (1 − P_B)^m]^{n+1}` is at least `1/4`, then the success probability of (C1) satisfies
`P ≥ 1/8` and the average photon number of (C4) satisfies
`Q̄ ≤ 8 (2mn(Q_L + 1) + 2m)`.

**Formalization Note** This is the assembly step of the scaling argument: it converts bounds on
the three factors of (C1) into a bound on (C4). `δ` is any real; at `n = 0` the first two factors
of (C1) are `1`. -/
theorem repeaterSuccess_ge_and_expectedPhotons_le (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 ≤ 1)
    (n m l : ℕ) (b : ℕ → ℕ) (δ : ℝ) (hm : 1 ≤ m)
    (hZ : 1 - zSuccess ε0 l b ≤ δ) (hX : 1 - xSuccess ε0 l b ≤ δ)
    (hδ : 2 * (m : ℝ) * n * δ ≤ 1 / 2)
    (hB : 1 / 4 ≤ (1 - (1 - bellSuccess ε0) ^ m) ^ (n + 1)) :
    1 / 8 ≤ repeaterSuccess ε0 n m l b ∧
      expectedPhotons ε0 n m l b ≤
        8 * (2 * (m : ℝ) * n * ((treeSize l b : ℝ) + 1) + 2 * m) := by sorry

end AllPhotonicRepeater
