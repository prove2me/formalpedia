-- Prove2me | Theorems.Thm_FDivToolkit_liminf_claim
-- name    : FDivToolkit.liminf_claim
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:27.65558+00:00
-- url     : https://prove2.me/theorems/f4ec0dc0-d69e-4bba-8fd8-651dd02b5537
-- title:
--   Proof of Proposition 3, p.33 — a lower bound on $F$
-- statement:
--   Let $H$ be a generating function that is continuously differentiable on $(\tilde y,\infty)$ for some $\tilde y>1$, with $\limsup_{y\to\infty}H'(y)/H(y)<\infty$. Then there exist $\bar y,\epsilon_1\in(0,\infty)$ such that
--   $$
--   F(y)\ge\epsilon_1\,y\,H(\log y)\qquad\text{for all }y\in(\bar y,\infty).
--   $$
--
--   This is the converse of (30) up to a constant, and it drives the lower bound in Proposition 3.
--
--   Differences from the source:
--   - encoding: lim sup_{y→∞} H′(y)/H(y) < ∞ → ∃ C, eventually H′(y) ≤ C H(y); reason: H > 0 on (0, ∞), so the two conditions are equivalent
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of Proposition 3, p.33

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Fh

open Filter Set

namespace FDivToolkit

/-- The lower bound on `F`, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of
Proposition 3, p.33: if `H` is continuously differentiable on `(ỹ, ∞)` and
`lim sup_{y→∞} H′(y)/H(y) < ∞`, there exist `ȳ, ϵ₁ ∈ (0, ∞)` with `F(y) ≥ ϵ₁ y H(log y)` for all
`y ∈ (ȳ, ∞)`.

**Formalization Note.** `H > 0` on `(0, ∞)`, so the lim sup condition is `H′(y) ≤ C H(y)` for large
`y`. -/
theorem liminf_claim {H : ℝ → ℝ} {ytilde : ℝ} (hH : IsAdmissibleH H) (hy : 1 < ytilde)
    (hC1 : ContDiffOn ℝ 1 H (Ioi ytilde))
    (hC : ∃ C : ℝ, ∀ᶠ y in atTop, deriv H y ≤ C * H y) :
    ∃ ybar : ℝ, 0 < ybar ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ y : ℝ, ybar < y → ε₁ * y * H (Real.log y) ≤ Fh H y := by sorry

end FDivToolkit
