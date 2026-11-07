-- Prove2me | Theorems.Thm_CritWinSpin_lemma_3_1_i
-- name    : CritWinSpin.lemma_3_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:16.422075+00:00
-- url     : https://prove2.me/theorems/914194cd-da0d-4d12-8a82-ae5b7f8cb83f
-- title:
--   Lemma 3.1(i), p.11 — unique type $p$, the expansion (1) of $I$, and $I(m)\ge\frac\tau2m^2+cm^{2p}$
-- statement:
--   Let $\rho$ satisfy the single-site GHS inequality. There is a unique integer $p\ge2$ such that $\kappa_4,\dots,\kappa_{2p-2}$ vanish and $\kappa_{2p}=\phi^{(2p)}(0)<0$. For this $p$, the constant $\kappa=-\kappa_{2p}/[(2p)!\,v^{2p}]$ is positive,
--   $$I(m)=\frac\tau2m^2+\kappa m^{2p}+O(m^{2p+2})\quad(m\to0),$$
--   and there is $c>0$ with
--   $$I(m)\ge\frac\tau2m^2+cm^{2p}\quad\text{for all }m\in[-1,1].$$
--
--   This fixes the critical exponent $d_p=(p-1)/p$ of the paper and is the global bound behind the convex envelope of §4.
--
--   Differences from the source:
--   - encoding: O(m^{2p+2}) as m → 0 → explicit C, m₀ > 0 with the bound on |m| ≤ m₀; reason: the definition of O at a point
--   - encoding: cumulant κ_j → the derivative ϕ^{(j)}(0); reason: the paper's own identification κ_{2p} = ϕ^{(2p)}(0)
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 3.1(i), p.11, eqs. (1), (11)

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 3.1(i)** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.11). Under
Definition 2.1 there is a unique type `p ≥ 2`; for it `κ = −κ_{2p}/[(2p)! v^{2p}] > 0`, the expansion (1)
`I(m) = (τ/2) m² + κ m^{2p} + O(m^{2p+2})` holds as `m → 0`, and `I(m) ≥ (τ/2) m² + c m^{2p}` on
`[−1, 1]`, eq. (11). -/
theorem lemma_3_1_i (S : SpinLaw) (hS : IsGHS S) :
    (∃! p : ℕ, IsTypeP S p) ∧
    ∀ p : ℕ, IsTypeP S p →
      0 < kappa S p ∧
      (∃ C m₀ : ℝ, 0 < C ∧ 0 < m₀ ∧ ∀ m : ℝ, |m| ≤ m₀ →
        |rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p)| ≤ C * |m| ^ (2 * p + 2)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, |m| ≤ 1 →
        (tau S / 2) * m ^ 2 + c * m ^ (2 * p) ≤ rateI S m) := by sorry

end CritWinSpin
