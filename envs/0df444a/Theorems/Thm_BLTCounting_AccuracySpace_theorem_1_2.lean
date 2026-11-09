-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_theorem_1_2
-- name    : BLTCounting.AccuracySpace.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:33.994462+00:00
-- url     : https://prove2.me/theorems/91109535-01b4-45b7-8928-f7f34e99288b
-- title:
--   Accuracy–space tradeoff for BLT approximation of the square-root sequence
-- statement:
--   Let $f[k]=4^{-k}\binom{2k}{k}$ be the square-root sequence. For every fixed $\varepsilon\in(0,1/2)$ there are constants $a_*=a_*(\varepsilon)>0$, $C_{\mathrm{lb}}=C_{\mathrm{lb}}(\varepsilon)>0$ and $n_0=n_0(\varepsilon)$ with the following property. For every $n\ge n_0$, every complex BLT sequence $c$ of recurrence order $d$ and every $\eta>0$, if
--   $$\|f-c\|_{\ell_2(0,n-1)}\le\eta\quad\text{and}\quad a_*\le\log(1/\eta)\le\Bigl(\frac12-\varepsilon\Bigr)\log\Bigl\lfloor\frac{n+1}2\Bigr\rfloor,$$
--   then
--   $$d\ge C_{\mathrm{lb}}\log(n)\log(1/\eta).$$
--
--   Here $\|f-c\|_{\ell_2(0,n-1)}^2=\sum_{k=0}^{n-1}|f[k]-c[k]|^2$, not divided by $n$, and logarithms are natural. The constants are chosen before $n$, $d$, $c$ and $\eta$, so $\eta$ and $c$ may vary with $n$. The theorem measures how much memory a buffered linear Toeplitz mechanism needs to reach a given coefficient accuracy.
--
--   Differences from the source:
--   - reading: "a BLT sequence of recurrence order $d$", with the streaming form (2) also described on printed p. 3 → the recurrence (3) with $q[1],\dots,q[d]$, unrestricted first $d$ coefficients, which is the meaning the source fixes on printed p. 4; reason: a one-state stream with feedthrough can have recurrence order two (for $W=u=v=\tau=1$ the coefficients are $2,1,1,\dots$), so the statement is about recurrence order, not about streaming state dimension
--   - reading: the display on printed p. 23, which drops the square on the left → $\sum_{k<n}|f[k]-c[k]|^2\le\eta^2$; reason: Theorem 1.2, the introduction and all calculations use this; only the typography differs
--   - encoding: $\eta$ implicitly positive through $\log(1/\eta)$ → an explicit hypothesis $\eta>0$; reason: only excludes the case where $\log(1/\eta)$ is undefined
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Theorem 1.2, printed p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

namespace BLTCounting.AccuracySpace

/-- Theorem 1.2 (Accuracy–space tradeoff), PDF p. 4: for every `ε ∈ (0, 1/2)` there are constants
`a_* > 0`, `C_lb > 0`, `n₀`, depending only on `ε`, such that for all `n ≥ n₀`, every BLT sequence `c`
of recurrence order `d` and every `η > 0`: if `‖f - c‖_{ℓ₂(0,n-1)} ≤ η` and
`a_* ≤ log(1/η) ≤ (1/2 - ε) log ⌊(n+1)/2⌋`, then `d ≥ C_lb log(n) log(1/η)`. -/
theorem theorem_1_2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ a Clb : ℝ, 0 < a ∧ 0 < Clb ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (c : ℕ → ℂ) (η : ℝ), 0 < η → IsBLT d c → coeffErr n sqrtSeq c ≤ η →
        a ≤ Real.log (1 / η) →
        Real.log (1 / η) ≤ (1 / 2 - ε) * Real.log (((n + 1) / 2 : ℕ) : ℝ) →
        Clb * Real.log n * Real.log (1 / η) ≤ (d : ℝ) := by sorry

end BLTCounting.AccuracySpace
