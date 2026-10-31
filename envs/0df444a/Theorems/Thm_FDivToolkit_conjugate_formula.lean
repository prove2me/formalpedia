-- Prove2me | Theorems.Thm_FDivToolkit_conjugate_formula
-- name    : FDivToolkit.conjugate_formula
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:53.728994+00:00
-- url     : https://prove2.me/theorems/94dde361-996e-46b9-9088-3df9736a3fdb
-- title:
--   Proof of Proposition 1, p.31 — the conjugate formula
-- statement:
--   Let $H$ be a generating function, $L=\lim_{y\to-\infty}H(y)$, and let $F$ be extended by $F(y)=+\infty$ for $y<0$. Then $F^*(x)=\sup_{y}(xy-F(y))$ is real-valued, with
--   $$
--   F^*(x)=x\exp(H^{-1}(x))-F(\exp(H^{-1}(x)))\quad(x>L),\qquad F^*(x)=-F(0)\quad(x\le L),
--   $$
--   and $F^*$ is differentiable on $\mathbb R$ with $(F^*)'(x)=\mathbf 1_{\{x>L\}}e^{H^{-1}(x)}$.
--
--   The derivative formula is what turns the conjugate into the worst-case density (6).
--
--   Differences from the source:
--   - encoding: L = lim_{y→−∞} H(y) and the test x > L → the test x ∈ range H; reason: range H = (L, ∞) for admissible H, as proved in the mission's sanity file
--   - encoding: F(y) = +∞ for y < 0, and F* : ℝ → ℝ with F*(x) = sup_{y∈ℝ}(xy − F(y)) → FstarE is the EReal supremum over y ≥ 0, Fstar its toReal; a clause states FstarE is neither ⊤ nor ⊥; reason: the values y < 0 contribute −∞; the clause is the paper's F* : ℝ → ℝ
--   - reading: F*(x) = −F(0) for all x ≤ L → for x ∉ range H, F(0) < ∞ and F* x = −(F0 H).toReal; reason: F*(x) is real, so −F(0) is real there; such x exists only for finite L, where F(0) ≤ −L
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of Proposition 1, p.31

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Fstar

open Set

namespace FDivToolkit

open Classical in

/-- The conjugate formula, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of
Proposition 1, p.31: `F*` is real-valued, `F*(x) = x exp(H⁻¹(x)) − F(exp(H⁻¹(x)))` for all `x > L`,
`F*(x) = −F(0)` for all `x ≤ L`, and `(F*)′(x) = 1_{x>L} e^{H⁻¹(x)}`.

**Formalization Note.** `x > L` is `x ∈ range H`. If some `x ≤ L` exists then `L` is finite, and then
`F(0) ≤ −L < ∞`, so `F(0)` is a real number in the second case. -/
theorem conjugate_formula {H : ℝ → ℝ} (hH : IsAdmissibleH H) :
    (∀ x : ℝ, FstarE H x ≠ ⊤ ∧ FstarE H x ≠ ⊥) ∧
    (∀ x ∈ range H,
      Fstar H x = x * Real.exp (Hinv H x) - Fh H (Real.exp (Hinv H x))) ∧
    (∀ x, x ∉ range H → F0 H ≠ ⊤ ∧ Fstar H x = -(F0 H).toReal) ∧
    (∀ x : ℝ, HasDerivAt (Fstar H) (if x ∈ range H then Real.exp (Hinv H x) else 0) x) := by sorry

end FDivToolkit
