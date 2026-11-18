-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_4_1
-- name    : CallCountPOPBR.Supplement.theorem_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-17T00:04:58.332354+00:00
-- url     : https://prove2.me/theorems/07a31384-1faf-44b3-90a1-1c2be3fbf993
-- title:
--   Theorem 4.1 — exact affine criterion
-- statement:
--   Let a terminating recursive procedure on inputs $X$ have ordered child list $(x_1,\ldots,x_{r(x)})$, returned value $V(x)\in\mathbb R$, and total invocation count $C(x)$. Fix $a,b\in\mathbb R$ with $a\ne0$. Then
--
--   $$
--   C(x)=aV(x)+b\quad\text{for every }x
--   $$
--
--   if and only if both of the following hold:
--
--   1. at every base case, $aV(x)+b=1$;
--   2. at every non-base case,
--
--      $$
--      a\left(V(x)-\sum_{i=1}^{r(x)}V(x_i)\right)=1+(r(x)-1)b.
--      $$
--
--   This criterion exactly characterises when returned values and invocation counts are affinely related.
--
--   Differences from the source:
--   - reading: the source calls $V(x)$ a numerical value without naming its scalar domain → $V,a,b$ are real-valued; reason: the real numbers support every affine operation used in the theorem and the divisions used immediately afterward in Corollary 4.2
--   - encoding: terminating recursive calls and the invocation count satisfying (5) → a well-founded child relation and its well-foundedly defined count; reason: this is the direct Lean representation of the source's terminating call tree
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Theorem 4.1, Eq. (6), p.8

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_RecProc

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

universe u

/-- **Theorem 4.1 (Exact affine criterion).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 4.1, p.8: "Fix constants a ≠ 0 and b.
The identity C(x) = aV(x) + b holds for every input if and only if both conditions hold: (i) for
every base-case input x, aV(x) + b = 1; (ii) for every non-base-case input x,
a(V(x) − ∑_{i=1}^{r(x)} V(x_i)) = 1 + (r(x) − 1)b. (6)"

`P` is a terminating recursive procedure with child lists `P.ch x` (`r(x)` = its length), `V` the
returned values and `P.count` the invocation count of Eq. (5).

**Formalization Note.** `r(x) − 1` is computed in `ℝ`. The hypothesis `a ≠ 0` is kept as printed. -/
theorem theorem_4_1 {X : Type u} (P : RecProc X) (V : X → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    (∀ x, (P.count x : ℝ) = a * V x + b) ↔
      ((∀ x, P.ch x = [] → a * V x + b = 1) ∧
       (∀ x, P.ch x ≠ [] →
          a * (V x - ((P.ch x).map V).sum) = 1 + (((P.ch x).length : ℝ) - 1) * b)) := by sorry

end CallCountPOPBR.Supplement
