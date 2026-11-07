-- Prove2me | Theorems.Thm_CubicProductLB_proposition_10
-- name    : CubicProductLB.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:07.934692+00:00
-- url     : https://prove2.me/theorems/8afcb2a4-3d14-4256-b28e-f43efa73d374
-- title:
--   Proposition 10 — restricted quadratic bias–rank
-- statement:
--   For every $\varepsilon > 0$ there is an integer $B(\varepsilon)$, depending on $\varepsilon$ only, such that every polynomial $Q$ of degree at most two over $\mathbb F_3$, in any number $n$ of variables, satisfying
--   $$\left| \mathbb E_{x \in X_n}\, \omega^{Q(x)} \right| \ge \varepsilon$$
--   agrees on $X_n$ with a sum of at most $\max(1, B(\varepsilon))$ products of affine forms. Consequently $Q$ depends on at most $2\max(1, B(\varepsilon))$ affine observations.
--
--   This is the statement that a quadratic with non-negligible bias has bounded complexity on the sign cube, independently of $n$; it is used during the elimination in the proof of Lemma 12.
--
--   Differences from the source:
--   - reading: "a sum of at most max(1, B(ε)) products of affine forms" → a sum of at most max(1, B) products A_ℓ·A′_ℓ of two affine forms; reason: the proof (p.14) obtains the sum from Lemma 9's ∑ A_ℓB_ℓ and says "Each product uses two affine factors", which is also what gives the bound 2 max(1, B(ε))
--   - encoding: an integer B(ε) → a natural number B; reason: max(1, B(ε)) absorbs any nonpositive value; same bound
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Proposition 10, Eq. (88), p.14

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_cubeAvg
import Definitions.Def_CubicProductLB_AffineForm
import Definitions.Def_CubicProductLB_DependsOnAtMost

namespace CubicProductLB

/-- Proposition 10 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Proposition 10, Eq. (88), p.14). For every `ε > 0` there is `B(ε)`, depending
on `ε` only, such that every `Q` of degree at most two with `|E_x ω^{Q(x)}| ≥ ε` agrees on `X_n` with a
sum of at most `max(1, B(ε))` products of affine forms, and depends on at most `2 max(1, B(ε))` affine
observations.

**Formalization Note** `B` comes before `n` and `Q`. "Integer `B(ε)`" is a natural number; the
`max(1, ·)` of the page absorbs a nonpositive value. -/
theorem proposition_10 (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (n : ℕ) (Q : MvPolynomial (Fin n) (ZMod 3)), Q.totalDegree ≤ 2 →
      ε ≤ ‖cubeAvg n fun x => ZMod.stdAddChar (MvPolynomial.eval x Q)‖ →
      (∃ m ≤ max 1 B, ∃ A A' : Fin m → AffineForm n,
        ∀ x ∈ signCube n,
          MvPolynomial.eval x Q = ∑ l, AffineForm.eval (A l) x * AffineForm.eval (A' l) x) ∧
      DependsOnAtMost (2 * max 1 B) (fun x => MvPolynomial.eval x Q) := by sorry

end CubicProductLB
