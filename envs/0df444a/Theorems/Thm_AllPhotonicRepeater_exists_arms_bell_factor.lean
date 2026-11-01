-- Prove2me | Theorems.Thm_AllPhotonicRepeater_exists_arms_bell_factor
-- name    : AllPhotonicRepeater.exists_arms_bell_factor
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:17.361756+00:00
-- url     : https://prove2.me/theorems/9e6b0b3d-0495-4d5d-8d2f-92e4cdd29641
-- title:
--   Eqs. (C1), (C2) with (C10): the Bell factor is at least $1/4$ with $m=O(n+1)$
-- statement:
--   Let $0\le\epsilon_0<1$ and $P_B=(1-\epsilon_0)^2/2$. There is a constant $C$ such that for every number $n$ of source nodes there is a number $m\ge1$ of Bell measurements per receiver node with
--   $$
--   m\le C\,(n+1)\qquad\text{and}\qquad \big[1-(1-P_B)^m\big]^{n+1}\ge\frac14 .
--   $$
--   The constant $C$ depends on $\epsilon_0$ only.
--
--   In (C1) the factor $[1-(1-P_B)^m]^{n+1}$ is the probability that all $n+1$ receiver nodes have a successful Bell measurement. The paper chooses $m$ by the approximate formula (C10); this item states the exact property of that choice that the scaling argument needs: the factor stays bounded below while $m$ grows at most linearly in the number of nodes.
--
--   Differences from the source:
--   - reading: $m\simeq\log_{1-P_B}[2n\ln P_L/(2n\ln P_L+(n+1)\ln(1-P_B))]$ (C10), an approximation → some $m\ge1$ with $m\le C(n+1)$ and $[1-(1-P_B)^m]^{n+1}\ge1/4$; reason: (C10) is a "≃" choice tied to the numerical (A4) route; this is the exact property of $m$ that bounding (C1) from below requires
--   - generalization: $\epsilon_0<0.5$ (standing assumption, p. 11) → $0\le\epsilon_0<1$; reason: the Bell factor needs only $P_B>0$; it specializes to the paper's range
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, Eqs. (C1), (C2), p. 11; Eq. (C10), p. 12

import Mathlib
import Definitions.Def_AllPhotonicRepeater_bellSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. C1, Eqs. (C1),
(C2), p. 11, with the choice of `m` in (C10), p. 12: for every per-photon loss probability
`0 ≤ ε0 < 1` there is a constant `C` such that for every number `n` of source nodes some number
`m ≥ 1` of Bell measurements per receiver node, with `m ≤ C (n + 1)`, makes the Bell factor of
(C1) at least `1/4`:

`[1 − (1 − P_B)^m]^{n+1} ≥ 1/4`, where `P_B = (1 − ε0)^2/2`.

**Formalization Note** (C10) chooses `m ≃ log_{1−P_B}[…]`, an approximation; this item states
the exact property of `m` the scaling argument needs. `C` is chosen after `ε0` and before `n`. -/
theorem exists_arms_bell_factor (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 < 1) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((n : ℝ) + 1) ∧
      1 / 4 ≤ (1 - (1 - bellSuccess ε0) ^ m) ^ (n + 1) := by sorry

end AllPhotonicRepeater
