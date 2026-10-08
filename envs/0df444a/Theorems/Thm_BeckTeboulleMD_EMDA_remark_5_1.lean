-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_remark_5_1
-- name    : BeckTeboulleMD.EMDA.remark_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:17.375184+00:00
-- url     : https://prove2.me/theorems/eb5c7f7a-8dae-4324-af72-41ce43fb0940
-- title:
--   Remark 5.1, p. 174 — the strong convexity inequality of Proposition 5.1(a) remains true for all x, y ∈ Δ
-- statement:
--   Let $\Delta = \{x \in \mathbb R^n : x \ge 0,\ \sum_j x_j = 1\}$ and $\psi_e(x) = \sum_j x_j \ln x_j$ with $0 \ln 0 = 0$.
--
--   1. For $x, y \in \Delta$ with the same support ($x_j = 0 \iff y_j = 0$ for every $j$),
--   $$\sum_{j=1}^n (x_j - y_j)\ln\frac{x_j}{y_j} \ge \|x - y\|_1^2,$$
--   where the terms with $x_j = y_j = 0$ are $0$.
--   2. $\psi_e$ is $1$-strongly convex on all of $\Delta$ with respect to $\|\cdot\|_1$: for $x, y \in \Delta$ and $a, b \ge 0$ with $a + b = 1$,
--   $$\psi_e(a x + b y) \le a\psi_e(x) + b\psi_e(y) - \tfrac12\, a b\, \|x - y\|_1^2.$$
--
--   The remark extends Proposition 5.1(a) from the relative interior to the closed simplex, which is what is needed to apply Theorems 4.1 and 4.2 with $X = \Delta$ and $\psi = \psi_e$.
--
--   **Formalization Note** When the supports differ, the left side of (1) is $+\infty$ on the page and "there is nothing to prove"; in Lean $\ln(x_j/0) = 0$, so that case is excluded by the support hypothesis rather than stated with a junk value. Part (2) is the remark's conclusion read through Proposition 5.1(a)'s "$\psi_e$ is 1-strongly convex", written out with $\|\cdot\|_1 = \sum_j |\cdot|$.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 174, Remark 5.1

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Remark 5.1, p. 174: the strong convexity inequality of Proposition 5.1(a) remains true on the
whole simplex `Δ` (with `0 ln 0 = 0`): (i) `∑_j (x_j − y_j) ln(x_j / y_j) ≥ ‖x − y‖₁²` for `x, y ∈ Δ`
with the same support (otherwise the left side is `+∞` on the page); (ii) `ψ_e` is `1`-strongly
convex on `Δ` with respect to `‖·‖₁`. -/
theorem remark_5_1 {n : ℕ} :
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), (∀ j, x j = 0 ↔ y j = 0) →
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by sorry

end BeckTeboulleMD.EMDA
