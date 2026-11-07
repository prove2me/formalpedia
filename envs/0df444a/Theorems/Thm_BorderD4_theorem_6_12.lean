-- Prove2me | Theorems.Thm_BorderD4_theorem_6_12
-- name    : BorderD4.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:18.244696+00:00
-- url     : https://prove2.me/theorems/b5c33d5c-ec43-409b-b2a3-540c144be9a4
-- title:
--   Theorem 6.12: the DiDIL theorem for bounded depth-4
-- statement:
--   In the situation of §6.3, suppose $f_0\ne 0$, and let $d_0$ be the least $d$ with $H_d(f_0)\ne 0$. Then there are integers $m,r\ge 1$ with
--   $$\log m=O\bigl(k4^k(k+\log\rho)\bigr),\qquad r=O\bigl(k4^k(\Delta+1)^{k+1}\bigr),$$
--   and nonzero polynomials $G_1,G_2\in\overline{C}_\Delta(m,r)$ such that $H_{d_0}(f_0)\cdot G_2=G_1$. The constants are absolute. This expresses the lowest component of $f_0$ as a ratio of two polynomials of low composition complexity.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - generalization: $f$ border computed by the circuit of §6.3 (p.62), with the form of Theorem 6.7 → any `LowWeightForm` of any polynomial $f$, with no circuit in the data; reason: §6.3 uses only that form (26)–(27); the form Theorem 6.7 produces is an instance
--   - encoding: the bounds "$\log m=O(\cdot)$, $r=O(\cdot)$" → one absolute constant $A$ chosen before $F$, $\sigma$, $k$, $\delta$, $\rho$, with the natural logarithm; reason: the page's constants are absolute (p.74); a change of base only changes $A$
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.12, p.63

import Mathlib
import Definitions.Def_BorderD4_LowWeightForm
import Definitions.Def_BorderD4_BorderCompClass
import Definitions.Def_BorderD4_homPart
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries
universe u v

namespace BorderD4

/-- Theorem 6.12, the DiDIL theorem for bounded depth-4: in the situation of §6.3, suppose `f₀ ≠ 0`, and let `d₀` be the
least `d` with `H_d(f₀) ≠ 0`. Then there are integers `m, r ≥ 1` with `log m = O(k 4^k (k + log ρ))` and
`r = O(k 4^k (Δ + 1)^{k+1})`, and nonzero `G_1, G_2` in the border class `C̄_Δ(m, r)` with `H_{d₀}(f₀) · G_2 = G_1`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.12, p.63.

**Formalization Note** The situation is a `LowWeightForm`, and `Δ = δ^k`. The `O`s hide one absolute constant, chosen
before `F`, `σ`, `k`, `δ`, `ρ` (p.74). `G_1`, `G_2` are polynomials in the free coordinates. -/
theorem theorem_6_12 : ∃ A : ℝ, 0 < A ∧ ∀ {F : Type u} [Field F] [IsAlgClosed F] [CharZero F]
    {σ : Type v} [Fintype σ] [DecidableEq σ] [Nonempty σ] {f : MvPolynomial σ F} {k δ ρ : ℕ},
    1 ≤ k → 1 ≤ δ → 1 ≤ ρ → ∀ (D : LowWeightForm f k δ ρ), D.f0 ≠ 0 →
    ∀ d₀ : ℕ, IsLeast {d | homPart d D.f0 ≠ 0} d₀ →
    ∃ (m r : ℕ) (G₁ G₂ : MvPolynomial D.T F), 1 ≤ m ∧ 1 ≤ r ∧
      Real.log m ≤ A * k * 4 ^ k * (k + Real.log ρ) ∧
      (r : ℝ) ≤ A * k * 4 ^ k * ((δ : ℝ) ^ k + 1) ^ (k + 1) ∧
      G₁ ≠ 0 ∧ G₂ ≠ 0 ∧
      G₁ ∈ BorderCompClass F D.T (δ ^ k) m r ∧ G₂ ∈ BorderCompClass F D.T (δ ^ k) m r ∧
      homPart d₀ D.f0 * G₂ = G₁ := by sorry

end BorderD4
