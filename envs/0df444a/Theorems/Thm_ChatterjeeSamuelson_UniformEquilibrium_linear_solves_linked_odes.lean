-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_linear_solves_linked_odes
-- name    : ChatterjeeSamuelson.UniformEquilibrium.linear_solves_linked_odes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:07:00.100435+00:00
-- url     : https://prove2.me/theorems/b24978cd-5048-4ec6-a416-31fb8fa163fc
-- title:
--   The linear strategies of Example 1 solve the linked differential equations (3a)–(3b)
-- statement:
--   Let $0 \le k \le 1$ and $\bar v > 0$, let both beliefs be uniform on $[0, \bar v]$, so $F_b(v) = F_s(v) = v/\bar v$ on $[0, \bar v]$ with density $f_b = f_s = 1/\bar v$, and let $S_{\mathrm{lin}}(v) = \frac{v}{2-k} + \frac{1-k}{2}\bar v$ and $B_{\mathrm{lin}}(v) = \frac{v}{1+k} + \frac{k(1-k)}{2(1+k)}\bar v$. Then:
--
--   1. **(3a)** for every seller value $y \in [0, \bar v]$ and every $x$ with $B_{\mathrm{lin}}(x) = S_{\mathrm{lin}}(y)$,
--   $$
--   k F_b(y)\, S_{\mathrm{lin}}'(y) + f_b(y)\, S_{\mathrm{lin}}(y) = x\, f_b(y);
--   $$
--   2. **(3b)** for every buyer value $x \in [0, \bar v]$ and every $y$ with $S_{\mathrm{lin}}(y) = B_{\mathrm{lin}}(x)$,
--   $$
--   (1-k)\bigl(1 - F_s(x)\bigr)\, B_{\mathrm{lin}}'(x) - f_s(x)\, B_{\mathrm{lin}}(x) = -\,y\, f_s(x).
--   $$
--
--   Here $x$ plays the role of the paper's $B^{-1}(S(y))$ and $y$ that of $S^{-1}(B(x))$. Equations (3a)–(3b) are the linked differential equations that Theorem 2 of the paper derives as necessary conditions for well-behaved equilibria; this statement records that the linear strategies of Example 1(a) satisfy them for uniform beliefs, which is the paper's justification of Example 1(a).
--
--   **Formalization Note** $F_b$ and $F_s$ are the distribution function of the uniform belief $U_{\bar v}$; the density $1/\bar v$ is written as a constant; derivatives are Mathlib's `deriv`. The inverse functions are replaced by bound variables with $B_{\mathrm{lin}}(x) = S_{\mathrm{lin}}(y)$, which determine them uniquely.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, pp. 842–843 [PDF 8–9], text following Example 1 ("By simple inspection one can check…"); equations (3a), (3b) from Theorem 2, p. 840 [PDF 6]

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.UniformEquilibrium

/-- The linear strategies of Example 1(a) solve the linked differential equations (3a) and
(3b) (Chatterjee & Samuelson, *Bargaining under Incomplete Information*, Oper. Res. 31(5)
1983, §3, pp. 842–843 [PDF 8–9], unnumbered text after Example 1: "By simple inspection
one can check that linear offer strategies above constitute solutions of Equations 3a and
3b when both distribution functions are linear."; equations (3a), (3b) are Theorem 2,
p. 840 [PDF 6]).

With `F_b = F_s = cdf (unif v̄)` (equal to `v/v̄` on `[0, v̄]`) and densities
`f_b = f_s = 1/v̄`, `Slin = sellerLinear k v̄`, `Blin = buyerLinear k v̄`:

* (3a) `k F_b(y) S′(y) + f_b(y) S(y) = B⁻¹(S(y)) f_b(y)`: for every seller value
  `y ∈ [0, v̄]` and every `x` with `Blin x = Slin y`,
  `k · F_b(y) · Slin′(y) + (1/v̄) · Slin(y) = x · (1/v̄)`;
* (3b) `(1 − k)(1 − F_s(x)) B′(x) − f_s(x) B(x) = −S⁻¹(B(x)) f_s(x)`: for every buyer value
  `x ∈ [0, v̄]` and every `y` with `Slin y = Blin x`,
  `(1 − k)(1 − F_s(x)) · Blin′(x) − (1/v̄) · Blin(x) = −(y · (1/v̄))`.

*Formalization Note.* `B⁻¹(S(y))` is written as a bound variable `x` with `Blin x = Slin y`
(both linear maps are injective for `0 ≤ k ≤ 1`, so `x` is unique), and `S⁻¹(B(x))` likewise.
`S′`, `B′` are Mathlib's `deriv`. The density `1/v̄` is written as a constant: it is the
derivative of `F(v) = v/v̄` on `(0, v̄)`. The identities are checked on the whole value
interval `[0, v̄]`, including values where the equilibrium strategy of Example 1(a) leaves
the linear branch. -/
theorem linear_solves_linked_odes (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar) :
    (∀ y ∈ Icc (0 : ℝ) vbar, ∀ x : ℝ, Shared.buyerLinear k vbar x = Shared.sellerLinear k vbar y →
        k * cdf (Shared.unif vbar) y * deriv (Shared.sellerLinear k vbar) y
            + (1 / vbar) * Shared.sellerLinear k vbar y = x * (1 / vbar)) ∧
      (∀ x ∈ Icc (0 : ℝ) vbar, ∀ y : ℝ, Shared.sellerLinear k vbar y = Shared.buyerLinear k vbar x →
        (1 - k) * (1 - cdf (Shared.unif vbar) x) * deriv (Shared.buyerLinear k vbar) x
            - (1 / vbar) * Shared.buyerLinear k vbar x = -(y * (1 / vbar))) := by sorry

end ChatterjeeSamuelson.UniformEquilibrium
