-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_finite_fiber
-- name    : ApproxPolySatCH.Main.finite_fiber
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:00.645909+00:00
-- url     : https://prove2.me/theorems/b70bf40b-f302-4b9e-aab8-7d533b3eb770
-- title:
--   Claim 9 — Finiteness of the prescribed fiber
-- statement:
--   Let $f=(f_1,\ldots,f_{n+1})$ be minimally dependent in $n\ge1$ variables over a field $k$, and put $\Delta=\max_i\deg f_i$. The bounded-degree relations preceding equation (17) exist: each nonzero $P_j(Y,U)$ has positive U-degree, vanishes at $(f_1,\ldots,f_n,X_j)$ and has total degree at most $\prod_{i=1}^n\deg f_i$. For any such choices, let $q_j$ be their leading U-coefficients and $h=\prod_jq_j$. Then
--   $$h\ne0,\qquad\deg h\le n\Delta^n,$$
--   and for every $a\in\overline k^n$ with $h(a)\ne0$,
--   $$V(f,a)=\{x\in L^n:f_i(x)=a_i\varepsilon\ (1\le i\le n)\}\quad\text{is finite}.$$
--   No positive-APS assumption is made. The relation-existence assertion records the immediately preceding source construction, so this statement does not assume that an algorithm has already supplied h.
--
--   This supplies the finiteness needed for every omitted-coordinate ordering, including negative inputs.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: The relations preceding (17) are chosen, and h is their product of leading coefficients. → Existence of the bounded relations is included, followed by the finiteness claim for every choice satisfying those identities.; reason: This makes the source’s construction explicit without assuming that h is an input or that fibers are already finite.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Claim 9, p.20 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=20

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem finite_fiber {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f) :
    Nonempty (LocalizationRelations f) ∧
    ∀ r : LocalizationRelations f, localizationProduct r ≠ 0 ∧
      (localizationProduct r).totalDegree ≤ n * maxDegree f ^ n ∧
      ∀ a : Fin n → Constants k,
        MvPolynomial.eval₂ (algebraMap k (Constants k)) a (localizationProduct r) ≠ 0 →
        (prescribedFiber f a).Finite := by sorry

end ApproxPolySatCH.Main
