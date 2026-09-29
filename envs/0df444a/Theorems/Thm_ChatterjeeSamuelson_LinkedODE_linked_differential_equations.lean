-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_LinkedODE_linked_differential_equations
-- name    : ChatterjeeSamuelson.LinkedODE.linked_differential_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:48:52.894425+00:00
-- url     : https://prove2.me/theorems/d20a3fd7-0506-4ad6-8732-164bd8538443
-- title:
--   Theorem 2 (Chatterjee–Samuelson): class $A$ equilibrium strategies satisfy the linked differential equations (3a)–(3b)
-- statement:
--   Consider sealed-offer bargaining between a seller with reservation price $v_s \in [\underline v_s, \bar v_s]$ and a buyer with reservation price $v_b \in [\underline v_b, \bar v_b]$: trade occurs iff the buyer's offer $b$ is at least the seller's ask $s$, at price $kb + (1-k)s$ with $0 \le k \le 1$. The buyer's belief about $v_s$ is a regular belief with distribution function $F_b$ and density $f_b$; the seller's belief about $v_b$ is a regular belief with distribution function $F_s$ and density $f_s$. Let $(S, B)$ be an equilibrium in which both strategies are of class $A$. Then:
--
--   1. **(3a)** For every seller value $y$ in an open interval $(a, c) \subseteq [\underline v_s, \bar v_s]$ on which $S$ is strictly increasing, and every buyer value $x \in [\underline v_b, \bar v_b]$ with $B(x) = S(y)$,
--   $$
--   k F_b(y) S'(y) + f_b(y) S(y) = x\, f_b(y).
--   $$
--   2. **(3b)** For every buyer value $x$ in an open interval $(a, c) \subseteq [\underline v_b, \bar v_b]$ on which $B$ is strictly increasing, and every seller value $y \in [\underline v_s, \bar v_s]$ with $S(y) = B(x)$,
--   $$
--   (1-k)\bigl(1 - F_s(x)\bigr) B'(x) - f_s(x) B(x) = -\,y\, f_s(x).
--   $$
--
--   Here $x$ in (3a) is the paper's $B^{-1}(S(y))$ and $y$ in (3b) is its $S^{-1}(B(x))$. The theorem turns the equilibrium problem into a pair of ordinary differential equations that link the two strategies; the paper's explicit equilibria (Example 1 for uniform beliefs) are solutions of this system.
--
--   **Formalization Note** $S'(y)$ is Lean's `deriv S y`, which the class $A$ assumption makes a genuine derivative at such $y$; no sign condition on $S'(y)$ is assumed. The inverses $B^{-1}$, $S^{-1}$ are not introduced as functions: the matching value is a bound variable, so the equations are asserted exactly where the inverse is defined.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 840 [PDF 6], Theorem 2, equations (3a) and (3b)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- **Theorem 2** (Chatterjee & Samuelson, *Bargaining under Incomplete Information*,
Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6]): "In a class A equilibrium, over intervals of
reservation prices for which the offer strategies are strictly increasing, S( ) and B( )
must satisfy the linked differential equations
  kF_b(y)S′(y) + f_b(y)S(y) = B⁻¹(S(y))f_b(y)   (3a)
  (1 − k)(1 − F_s(x))B′(x) − f_s(x)B(x) = −S⁻¹(B(x))f_s(x).   (3b)"

Setting: `0 ≤ k ≤ 1`; seller values in `[loS, hiS]`, buyer values in `[loB, hiB]`; the
buyer's belief `μb` about `v_s` is regular on `[loS, hiS]` with CDF `F_b = cdf μb` and
density `fb`; the seller's belief `μs` about `v_b` is regular on `[loB, hiB]` with
`F_s = cdf μs` and density `fs`; `(S, B)` is an equilibrium and both strategies are of
class `A`. Then
* (3a) holds at every seller value `y` interior to an open interval `(a, c) ⊆ [loS, hiS]`
  on which `S` is strictly increasing, for every buyer value `x ∈ [loB, hiB]` with
  `B x = S y` (the paper's `B⁻¹(S(y))`);
* (3b) holds at every buyer value `x` interior to an open interval `(a, c) ⊆ [loB, hiB]`
  on which `B` is strictly increasing, for every seller value `y ∈ [loS, hiS]` with
  `S y = B x` (the paper's `S⁻¹(B(x))`).

*Formalization Note.* `S′(y)` is `deriv S y`; class `A` makes `S` differentiable there.
No sign condition on `S′(y)` is assumed. `B⁻¹` and `S⁻¹` are not introduced as functions:
the inverse image is a bound variable, so the equations are asserted exactly where the
paper's inverse is defined. -/
theorem linked_differential_equations (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb fs S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hμs : RegularBelief μs loB hiB fs)
    (hEq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B)
    (hS : ClassA S loS hiS) (hB : ClassA B loB hiB) :
    (∀ a c y : ℝ, loS ≤ a → c ≤ hiS → y ∈ Ioo a c → StrictMonoOn S (Ioo a c) →
      ∀ x ∈ Icc loB hiB, B x = S y →
        k * cdf μb y * deriv S y + fb y * S y = x * fb y) ∧
    (∀ a c x : ℝ, loB ≤ a → c ≤ hiB → x ∈ Ioo a c → StrictMonoOn B (Ioo a c) →
      ∀ y ∈ Icc loS hiS, S y = B x →
        (1 - k) * (1 - cdf μs x) * deriv B x - fs x * B x = -(y * fs x)) := by sorry

end ChatterjeeSamuelson.LinkedODE
