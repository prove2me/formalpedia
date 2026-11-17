-- Prove2me | Theorems.Thm_AddXnor_Supplement_theorem_3
-- name    : AddXnor.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:32:02.46213+00:00
-- url     : https://prove2.me/theorems/ddf3883e-c15b-483e-a57d-cc6e1c3ae021
-- title:
--   Theorem 3 — Run-product formula
-- statement:
--   Let $N\ge2$, $m\ge2$, and let $x\in\{0,1\}^{N-1}$ have maximal addition-run lengths $z_1,\ldots,z_r$. The signed bit-$1$ correlation satisfies
--   $$
--   \operatorname{Cor}(x)=\prod_{t=1}^r c(z_t),\qquad c(z)=2^{-z/2}\cos(z\pi/4).
--   $$
--   Furthermore, $|c(z)|\le2^{-z/2}$, $c(z)=0$ exactly when $z\equiv2\pmod4$, and
--   $$
--   |\operatorname{Cor}(x)|\le2^{-\frac12\sum_tz_t}=2^{-\mathrm{wt}(\bar x)/2}.
--   $$
--
--   Thus the correlation loses exactly half a bit of its envelope per addition. The all-XNOR string has the empty run profile and empty product $1$.
--
--   Differences from the source:
--   - encoding: $m$-bit words and operator strings → `BitVec m` operands and functions `Fin (N-1) → Bool`; reason: finite-type encoding with the same instances, with `false` = addition and `true` = XNOR
-- source:
--   Wang, Lv, Shen, Zhang, manuscript (sha256 405d6dda…), Theorem 3, pp.15–16 (PDF pp.15–16)

import Mathlib
import Definitions.Def_AddXnor_Supplement_core

set_option autoImplicit false

namespace AddXnor.Supplement

/-- **Theorem 3 (Run-product formula)** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*,
manuscript, sha256 405d6dda..., Theorem 3, pp.15--16 (PDF pp.15--16)).

For every admissible chain, the signed bit-1 correlation factors over the maximal addition runs.
The remaining clauses give the exact closed form, its zeros, and the half-bit-per-addition bound.
The all-XNOR string has an empty run profile, so its product is `1`. -/
theorem theorem_3 (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (x : Fin (N - 1) → Bool) :
    correlation (m := m) x = ((additionRuns x).map runCorrelation).prod ∧
    (∀ z : ℕ,
      |runCorrelation z| ≤ Real.rpow 2 (-(z : ℝ) / 2) ∧
      (runCorrelation z = 0 ↔ z % 4 = 2)) ∧
    |correlation (m := m) x| ≤
      Real.rpow 2 (-((additionRuns x).sum : ℝ) / 2) ∧
    Real.rpow 2 (-((additionRuns x).sum : ℝ) / 2) =
      Real.rpow 2 (-((N - 1 - weight x : ℕ) : ℝ) / 2) := by sorry

end AddXnor.Supplement
