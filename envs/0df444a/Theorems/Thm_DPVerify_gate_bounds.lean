-- Prove2me | Theorems.Thm_DPVerify_gate_bounds
-- name    : DPVerify.gate_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:23.587068+00:00
-- url     : https://prove2.me/theorems/b5c10587-fcfa-41ae-8e05-b5c45078c698
-- title:
--   Proof of Theorem 4.1, p.13 — gate bounds $\mathbb E\,G\le\kappa p\pi$, $\mathbb E|G(p,\cdot)-G(q,\cdot)|\le2\pi\kappa|p-q|$ (corrected: the $\cot^{-1}$ identity for $x>0$)
-- statement:
--   Let $\kappa>0$, $L\ge1$, let $u$ be uniform on $\{1/L,\dots,1\}$, and let $G(p,u)=\kappa^2p^2/(u^2+\kappa^2p^2)$. Writing $\cot^{-1}(y)=\arctan(1/y)$ for $y>0$:
--
--   1. for $p\ge0$: $\displaystyle \mathbb E_u\,G(p,u)\le\int_0^1G(p,u)\,du=\kappa p\cot^{-1}(\kappa p)\le\kappa p\pi$ (both sides of the equality are $0$ at $p=0$);
--   2. for $0\le q\le p$: $\displaystyle \mathbb E_u|G(p,u)-G(q,u)|=\int_q^p\mathbb E_u\Bigl[\frac{\partial G}{\partial x}(x,u)\Bigr]dx$;
--   3. wherever $u\ne0$ or $x\ne0$: $\displaystyle\frac{\partial G}{\partial x}(x,u)=\frac{2\kappa^2xu^2}{(u^2+\kappa^2x^2)^2}$;
--   4. for $x\ge0$: $\displaystyle\frac{2\kappa^2xu^2}{(u^2+\kappa^2x^2)^2}\le\frac{2\kappa^2x}{u^2+\kappa^2x^2}$;
--   5. for $x>0$: $\displaystyle\int_0^1\frac{2\kappa^2x}{u^2+\kappa^2x^2}\,du=2\kappa\cot^{-1}(\kappa x)\le2\pi\kappa$;
--   6. for $p,q\ge0$: $\mathbb E_u|G(p,u)-G(q,u)|\le2\pi\kappa|p-q|$.
--
--   These are the analytic facts behind the completeness and soundness bounds of Theorem 4.1: the gate is small when the message is unlikely, and it moves by at most $2\pi\kappa$ times the change in the message probability.
--
--   Differences from the source:
--   - correction: $\int_0^1\frac{2\kappa^2x}{u^2+\kappa^2x^2}du=2\kappa\cot^{-1}(\kappa x)$ → the identity for $x>0$ only; reason: at $x=0$ the integrand vanishes and the integral is $0$, while $2\kappa\cot^{-1}(0)=\kappa\pi$ under both conventions of footnote 7
--   - encoding: $\cot^{-1}$ with range $(-\pi/2,\pi/2]$ or $(0,\pi]$ (footnote 7) → $\arctan(1/y)$ for $y>0$; reason: both conventions agree with it for $y>0$
--   - encoding: $\mathbb E_{r\sim\mathcal R}$ of a function of $U_m(r)$ → the average over the grid $\{1/L,\dots,1\}$; reason: $U_m(r)$ is uniform on that grid
--   - encoding: $\partial G/\partial x$ for all $(x,u)$ → the derivative at points with $u\ne0$ or $x\ne0$; reason: at $u=x=0$ the gate is not continuous in $x$ and the formula is undefined
--   - generalization: suppose WLOG $p_S(m)\ge\mu(m)$; the bound $2\pi\kappa(p_S(m)-\mu(m))$ → $2\pi\kappa|p-q|$ for all $p,q\ge0$; reason: covers both orders, as the page's WLOG intends
--   - generalization: $L\ge|\mathcal M|$ the smallest such power of two, a fixed constant $\kappa$, $p$ a probability → any integer $L\ge1$, any $\kappa>0$, any real $p\ge0$; reason: the page's values are instances; the bounds use only that the grid lies in $(0,1]$
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_DPVerify_gate
import Definitions.Def_DPVerify_gridMean

set_option autoImplicit false

namespace DPVerify

/-- §4, proof of Theorem 4.1, the gate displays (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.13 = PDF p.16), for
`G(p, u) = κ²p² / (u² + κ²p²)` with `κ > 0` and `u ∼ Unif{1/L, …, 1}`:
1. for `p ≥ 0`: `E_u G(p, u) ≤ ∫₀¹ G(p, u) du = κp cot⁻¹(κp) ≤ κpπ`;
2. for `0 ≤ q ≤ p`: `E_u |G(p, u) − G(q, u)| = ∫_q^p E_u[∂G/∂x (x, u)] dx`;
3. `∂G/∂x (x, u) = 2κ²xu² / (u² + κ²x²)²` (wherever `u ≠ 0` or `x ≠ 0`);
4. for `x ≥ 0`: `2κ²xu² / (u² + κ²x²)² ≤ 2κ²x / (u² + κ²x²)`;
5. for `x > 0`: `∫₀¹ 2κ²x / (u² + κ²x²) du = 2κ cot⁻¹(κx) ≤ 2πκ`;
6. for `p, q ≥ 0`: `E_u |G(p, u) − G(q, u)| ≤ 2πκ |p − q|`.

**Formalization Note** `cot⁻¹(y)` is `arctan(1/y)` for `y > 0`, where both conventions of footnote
7 agree; in item 1 at `p = 0` both sides are `0`. Item 5 is stated for `x > 0`: at `x = 0` the
integral is `0` while `2κ cot⁻¹(0) = κπ` (correction). Item 6 replaces the page's
"WLOG `p_S(m) ≥ μ(m)`" by `|p − q|`. -/
theorem gate_bounds (κ : ℝ) (hκ : 0 < κ) (L : ℕ) (hL : 1 ≤ L) :
    (∀ p : ℝ, 0 ≤ p →
      gridMean L (gate κ p) ≤ ∫ u in (0 : ℝ)..1, gate κ p u ∧
      ∫ u in (0 : ℝ)..1, gate κ p u = κ * p * Real.arctan (1 / (κ * p)) ∧
      κ * p * Real.arctan (1 / (κ * p)) ≤ κ * p * Real.pi) ∧
    (∀ p q : ℝ, 0 ≤ q → q ≤ p →
      gridMean L (fun u => |gate κ p u - gate κ q u|) =
        ∫ x in q..p, gridMean L (fun u => 2 * κ ^ 2 * x * u ^ 2 / (u ^ 2 + κ ^ 2 * x ^ 2) ^ 2)) ∧
    (∀ x u : ℝ, (u ≠ 0 ∨ x ≠ 0) →
      HasDerivAt (fun y => gate κ y u)
        (2 * κ ^ 2 * x * u ^ 2 / (u ^ 2 + κ ^ 2 * x ^ 2) ^ 2) x) ∧
    (∀ x u : ℝ, 0 ≤ x →
      2 * κ ^ 2 * x * u ^ 2 / (u ^ 2 + κ ^ 2 * x ^ 2) ^ 2 ≤
        2 * κ ^ 2 * x / (u ^ 2 + κ ^ 2 * x ^ 2)) ∧
    (∀ x : ℝ, 0 < x →
      ∫ u in (0 : ℝ)..1, 2 * κ ^ 2 * x / (u ^ 2 + κ ^ 2 * x ^ 2) =
        2 * κ * Real.arctan (1 / (κ * x)) ∧
      2 * κ * Real.arctan (1 / (κ * x)) ≤ 2 * Real.pi * κ) ∧
    (∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
      gridMean L (fun u => |gate κ p u - gate κ q u|) ≤ 2 * Real.pi * κ * |p - q|) := by sorry

end DPVerify
