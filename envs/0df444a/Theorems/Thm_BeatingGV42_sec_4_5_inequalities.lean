-- Prove2me | Theorems.Thm_BeatingGV42_sec_4_5_inequalities
-- name    : BeatingGV42.sec_4_5_inequalities
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:40.886746+00:00
-- url     : https://prove2.me/theorems/05832310-6d2d-44e4-8731-01290654f532
-- title:
--   §4.5 inequalities on $I=[0.39,0.48]$ — $F>0$, $1-\delta<a_{GV}(\delta)<\frac{49}{48}(1-\delta)<1$, $a_{GV}>1/3$
-- statement:
--   With $h$, $a_{GV}$ and $F$ as in §4.5 and $I=[0.39,0.48]$:
--
--   1. $h(x)+x\ln\frac{41}{49}\le\ln\frac{90}{49}$ for every $x\in[0,1]$, with equality at $x=41/90$ (its maximum);
--   2. $\ln\frac{90}{49}<\frac{\ln49}6$ (equivalently $90^6<49^7$);
--   3. for every $\delta\in I$: $F(\delta)>0$; $a_{GV}(\delta)>1-\delta$; $a_{GV}(\delta)<\frac{49}{48}(1-\delta)\le\frac{49}{48}\cdot0.61<1$; and $a_{GV}(\delta)>1-\delta\ge0.52>1/3$.
--
--   These place the degree fraction $a_{GV}(\delta)$ inside the range $(1-\delta,1)$ that Proposition 4.9 needs ($\delta>1-a$, $a<1$, and $a>1/3=2/(\sqrt{49}-1)$).
--
--   **Formalization Note** $h$ is `Real.binEntropy`, $F$ is `Fgap`. Every printed clause of the paragraph is a conjunct.
--
--   Differences from the source:
--   - reading: the function h(x) + x ln(41/49) attains its maximum at x = 41/90, where its value is ln(90/49) → ∀ x ∈ [0, 1], h(x) + x ln(41/49) ≤ ln(90/49), and equality at x = 41/90; reason: h is defined on [0, 1]; a maximum attained at 41/90 with value ln(90/49) is exactly these two facts
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.5, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_BeatingGV42_aGV
import Definitions.Def_BeatingGV42_Fgap

set_option autoImplicit false

namespace BeatingGV42

/-- **The §4.5 inequalities on `I = [0.39, 0.48]`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.5, p.24 (PDF p.26)):
1. "Consequently, F(δ) > 0 throughout I";
2. "the function h(x) + x ln(41/49) attains its maximum at x = 41/90, where its value is ln(90/49)",
   and "ln(90/49) < ln 49/6" ("Since 90^6 < 49^7");
3. "Therefore, a_GV(δ) > 1 − δ";
4. "a_GV(δ) < (49/48)(1 − δ) ≤ (49/48) · 0.61 < 1";
5. "In particular, a_GV(δ) > 1 − δ ≥ 0.52 > 1/3 for every δ ∈ I."

**Formalization Note** `h = Real.binEntropy`, `F = Fgap`. Clause 2 is stated as the bound
`h(x) + x ln(41/49) ≤ ln(90/49)` for every `x ∈ [0, 1]` with equality at `x = 41/90`. -/
theorem sec_4_5_inequalities :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, Real.binEntropy x + x * Real.log (41 / 49) ≤ Real.log (90 / 49)) ∧
    Real.binEntropy (41 / 90) + 41 / 90 * Real.log (41 / 49) = Real.log (90 / 49) ∧
    Real.log (90 / 49) < Real.log 49 / 6 ∧
    ∀ δ ∈ Set.Icc (39 / 100 : ℝ) (48 / 100),
      0 < Fgap δ ∧ 1 - δ < aGV δ ∧ aGV δ < 49 / 48 * (1 - δ) ∧
      49 / 48 * (1 - δ) ≤ 49 / 48 * (61 / 100) ∧ (49 / 48 : ℝ) * (61 / 100) < 1 ∧
      52 / 100 ≤ 1 - δ ∧ 1 / 3 < aGV δ := by sorry

end BeatingGV42
