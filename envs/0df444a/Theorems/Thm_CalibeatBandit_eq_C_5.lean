-- Prove2me | Theorems.Thm_CalibeatBandit_eq_C_5
-- name    : CalibeatBandit.eq_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:33.653704+00:00
-- url     : https://prove2.me/theorems/25ed34f4-11ba-4ee7-a3d7-9371f4fafece
-- title:
--   Eq. (C.5) — second-order bound $\frac1\eta\log\sum_jx(j)e^{\eta v(j)}-\langle x,v\rangle\le(e-2)\eta\sum_jx(j)v(j)^2$
-- statement:
--   Let $x\in\Delta(\mathcal A)$, $\eta>0$ and $v\in\mathbb R^K$ with $0\le\eta v(j)\le1$ for every $j$. Then
--   $$\frac1\eta\log\Bigl(\sum_jx(j)e^{\eta v(j)}\Bigr)-\langle x,v\rangle\le\frac1\eta\log\Bigl(1+\eta\langle x,v\rangle+(e-2)\eta^2\sum_jx(j)v(j)^2\Bigr)-\langle x,v\rangle\le(e-2)\eta\sum_jx(j)v(j)^2 .$$
--
--   The first inequality uses $e^z\le1+z+(e-2)z^2$ for $z\le1$, the second $\log(1+x)\le x$. Combined with (C.4) it reduces the regret on corrected rewards to a second moment.
--
--   Differences from the source:
--   - generalization: the algorithm's $x_t$, $v_t$, for which the paper derives $0\le\eta v_t(j)\le1$ from $p_t(j)\ge4\eta$ and $\eta\le1/8$ → any $x\in\Delta(\mathcal A)$ and $v$ with $0\le\eta v(j)\le1$; reason: the algorithm's quantities satisfy the hypothesis, as the page shows
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: actions $\mathcal A=[K]$ → `Fin K`; reason: a relabelling; same instances
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, display (C.5), p.34 (PDF 34)

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **(C.5): the second-order bound on the log-moment** (§C.2, proof of Lemma C.3, p.34).
For `x ∈ Δ(𝒜)`, `η > 0` and a vector `v` with `0 ≤ ηv(j) ≤ 1` for every `j`,
`(1/η) log(∑_j x(j) exp(ηv(j))) − ⟨x, v⟩
  ≤ (1/η) log(1 + η⟨x, v⟩ + (e − 2)η² ∑_j x(j)v(j)²) − ⟨x, v⟩ ≤ (e − 2)η ∑_j x(j)v(j)²`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.5), p.34.

**Formalization Note.** The paper derives `0 ≤ ηv_t(j) ≤ 1` for the algorithm's `v_t` from
`p_t(j) ≥ 4η` and `η ≤ 1/8`; here that range is the hypothesis, for arbitrary `x`, `v`. `log` is
`Real.log`, `e` is `Real.exp 1`, `⟨x, v⟩` is `x ⬝ᵥ v`. -/
theorem eq_C_5 {K : ℕ} (η : ℝ) (hη : 0 < η) (x v : Fin K → ℝ) (hx : IsProbVec x)
    (hv : ∀ j, 0 ≤ η * v j ∧ η * v j ≤ 1) :
    1 / η * Real.log (∑ j, x j * Real.exp (η * v j)) - x ⬝ᵥ v
        ≤ 1 / η * Real.log (1 + η * (x ⬝ᵥ v) + (Real.exp 1 - 2) * η ^ 2 * ∑ j, x j * v j ^ 2)
          - x ⬝ᵥ v ∧
    1 / η * Real.log (1 + η * (x ⬝ᵥ v) + (Real.exp 1 - 2) * η ^ 2 * ∑ j, x j * v j ^ 2)
          - x ⬝ᵥ v
        ≤ (Real.exp 1 - 2) * η * ∑ j, x j * v j ^ 2 := by sorry

end CalibeatBandit
