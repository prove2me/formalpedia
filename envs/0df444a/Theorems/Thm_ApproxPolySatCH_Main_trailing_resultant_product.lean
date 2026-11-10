-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_trailing_resultant_product
-- name    : ApproxPolySatCH.Main.trailing_resultant_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:39.554086+00:00
-- url     : https://prove2.me/theorems/ca2a6375-9478-41f3-81fa-7eb2a4044533
-- title:
--   Lemma 11 — Trailing resultant with multiplicities
-- statement:
--   In the minimally dependent setting with $n\ge1$, choose any ordering of $f$ and any $a\in\overline k^n$. Construct the exact homogenized and perturbed forms in equations (20)–(21). If $V=V(f,a)$ is finite and nonempty, then
--   $$R_0\ne0,\qquad\operatorname{TT}_W\operatorname{TT}_T R_0=c\prod_{x\in V}(Z-f_{n+1}(x))^{m_x},$$
--   where $c\in L^\times$ and every $m_x$ is a positive integer. Epsilon is evaluated in the valued algebraic closure and Z remains a polynomial variable. The first trailing operation is in T.
--
--   This includes all affine points with multiplicities and imposes no exclusion of projective points at infinity.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: The resultants (20)–(21), a finite nonempty V, nonzero scalar and positive integral point multiplicities. → A universally specialized integer resultant, T-trailing then W-trailing, and a finite-set product with natural multiplicities strictly greater than zero.; reason: Positive natural multiplicities are exactly positive integers; c lies in the font-distinguished valued closure, and no infinity-point exclusion is added.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Lemma 11, p.21 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=21

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem trailing_resultant_product {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f)
    (a : Fin n → Constants k) (hfinite : (prescribedFiber f a).Finite)
    (hnonempty : (prescribedFiber f a).Nonempty) :
    R0 f a ≠ 0 ∧ ∃ (c : ValuedClosure k) (mult : (Fin n → ValuedClosure k) → ℕ), c ≠ 0 ∧
      (∀ x ∈ prescribedFiber f a, 0 < mult x) ∧
      asZPolynomial (twiceTrailing (R0 f a)) = Polynomial.C c *
        ∏ x ∈ hfinite.toFinset,
          (Polynomial.X - Polynomial.C (evaluateValued (f (Fin.last n)) x)) ^ mult x := by sorry

end ApproxPolySatCH.Main
