-- Prove2me | Theorems.Thm_DRBaseline_proposition_1
-- name    : DRBaseline.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:19.552672+00:00
-- url     : https://prove2.me/theorems/76b13d60-7f07-4761-9374-fd33b917efea
-- title:
--   Proposition 1 (corrected: $s^*=0$ above $\omega_1$, $\omega_1\ge\min(b,2\Omega)$, $S^*>0\iff s^*>0$ for $r,\omega>0$): three regimes of the customer's response
-- statement:
--   Let $\Omega>0$, $c_s>0$, and fix a baseline $b\ge0$, a rebate $r\ge0$ and a demand realization $\omega\in[0,2\Omega]$. Let $\omega_1=\omega_1(b,r)$ and $\omega_2=\omega_2(b,r)$ be the thresholds of p.OA1. Then:
--
--   1. $\omega_2\le\omega_1$ and $\min(b,2\Omega)\le\omega_1$;
--   2. if $\omega>\omega_1$, the customer's problem $\max_{s\le\omega}C_c(s)$ has the unique solution $s^*=0$ (no reduction);
--   3. if $\omega=\omega_1<2\Omega$, then $s^*=0$ is a solution;
--   4. if $\omega_2<\omega<\omega_1$, then $r/c_s\le\omega$ and the unique solution is $s^*=r/c_s$ (partial reduction);
--   5. if $\omega\le\omega_2$, then $s^*=\omega$ is a solution (full reduction), and it is the unique one when $\omega<\omega_2$;
--   6. if $r>0$ and $\omega>0$, every solution $s^*$ satisfies $S(s^*)>0\iff s^*>0$.
--
--   The customer's actual reduction is therefore not monotone in its demand: a customer far above the baseline does not reduce at all, because it would have to shift a large amount before being paid anything.
--
--   Differences from the source:
--
--   - correction: s∗ = 0 if ω ≥ ω1(b,r) → s∗ = 0 is the unique solution for ω > ω₁, and a solution at ω = ω₁ < 2Ω; reason: at Ω = c_s = r = 1, b = 2, ω = 2 = ω₁ (the cap binds): C_c(1) = 1/2 > 0 = C_c(0)
--   - correction: ω1(·) ≥ b → ω₁ ≥ min(b, 2Ω); reason: ω₁ is capped at 2Ω: Ω = c_s = r = 1, b = 3 gives ω₁ = 2 < 3
--   - correction: S∗ > 0 if and only if s∗ > 0 → the same for r > 0 and ω > 0; reason: at r = 0, b = 1, ω = 1/2 the solution is s∗ = 0 while S∗ = 1/2 > 0; at ω = 0, b = r = 1, s∗ = 0 while S∗ = 1
--   - encoding: s∗(·) = ω if ω ≤ ω2(·) → ω is a solution for ω ≤ ω₂, the unique one for ω < ω₂; reason: at ω = ω₂ = ω_A both 0 and ω can be maximizers, so 'the' arg max is read as 'a' maximizer there
--   - encoding: s∗ = arg max, a single function → every solution of the customer's problem (IsCustomerOptimal), with uniqueness where it holds; reason: the arg max has ties at up to two ω per (b, r); any two selections differ on a null set, so every integral is the paper's
--   - encoding: a given baseline b, rebate r, demand ω → b ≥ 0, r ≥ 0, ω ∈ [0, 2Ω]; reason: the firm's domain and the support of f (p.7)
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Proposition 1, pp.11–12; proof p.OA1

import Mathlib
import Definitions.Def_DRBaseline_IsCustomerOptimal
import Definitions.Def_DRBaseline_omega1
import Definitions.Def_DRBaseline_omega2

namespace DRBaseline

/-- **Proposition 1 (corrected): the three regimes of the customer's demand reduction.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Proposition 1, pp.11–12; proof p.OA1.

Fix `Ω > 0`, `c_s > 0`, a baseline `b ≥ 0`, a rebate `r ≥ 0` and a demand realization
`ω ∈ [0, 2Ω]`. With `ω₁`, `ω₂` the thresholds of p.OA1:
1. `ω₂ ≤ ω₁` and `min(b, 2Ω) ≤ ω₁`;
2. if `ω₁ < ω`, the customer's problem has the unique solution `0`;
3. if `ω = ω₁ < 2Ω`, `0` is a solution;
4. if `ω₂ < ω < ω₁`, then `r/c_s ≤ ω` and `r/c_s` is the unique solution;
5. if `ω ≤ ω₂`, `ω` is a solution, and the unique one when `ω < ω₂`;
6. if `r > 0` and `ω > 0`, every solution `x` has `S(x) > 0 ↔ x > 0`.

**Formalization Note** Corrections of the printed statement: the first bullet's "if ω ≥ ω1" is
split into the strict case (unique `0`) and `ω = ω₁ < 2Ω` (at `ω = ω₁ = 2Ω` the cap binds and
`0` can fail to be optimal); "ω1(·) ≥ b" becomes `ω₁ ≥ min(b, 2Ω)` (`ω₁` is capped at `2Ω`);
the last bullet assumes `r > 0`, `ω > 0` (at `r = 0` or `ω = 0` the customer shifts nothing
while `S = (b − ω)⁺` may be positive). -/
theorem proposition_1 (Ω cs b r ω : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hω0 : 0 ≤ ω) (hω2 : ω ≤ 2 * Ω) :
    (omega2 Ω cs b r ≤ omega1 Ω cs b r ∧ min b (2 * Ω) ≤ omega1 Ω cs b r) ∧
    (omega1 Ω cs b r < ω → ∀ x : ℝ, IsCustomerOptimal cs b r ω x ↔ x = 0) ∧
    (ω = omega1 Ω cs b r → omega1 Ω cs b r < 2 * Ω → IsCustomerOptimal cs b r ω 0) ∧
    (omega2 Ω cs b r < ω → ω < omega1 Ω cs b r →
      r / cs ≤ ω ∧ ∀ x : ℝ, IsCustomerOptimal cs b r ω x ↔ x = r / cs) ∧
    (ω ≤ omega2 Ω cs b r → IsCustomerOptimal cs b r ω ω) ∧
    (ω < omega2 Ω cs b r → ∀ x : ℝ, IsCustomerOptimal cs b r ω x ↔ x = ω) ∧
    (0 < r → 0 < ω → ∀ x : ℝ, IsCustomerOptimal cs b r ω x →
      (0 < estReduction b ω x ↔ 0 < x)) := by sorry

end DRBaseline
