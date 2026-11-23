-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_positive_valuation_implies_APS
-- name    : ApproxPolySatCH.Main.positive_valuation_implies_APS
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:52.164393+00:00
-- url     : https://prove2.me/theorems/95c66cdf-e26d-4743-9e3e-bb23a1b70c3a
-- title:
--   Proposition 4 interface — a positive-valuation fiber point certifies APS
-- statement:
--   Let $f$ be minimally dependent in $n\ge1$ variables over a field $k$, with irreducible annihilator $H$ and its scalar-extended presentation. Write $K=\overline k$ and let $L=\overline{K(\varepsilon)}$ carry the epsilon valuation $\nu$. Fix $a\in K^n$. If there is a point $x\in L^n$ in the prescribed fiber
--   $$V(f,a)=\{x:f_i(x)=a_i\varepsilon\quad(1\le i\le n)\}$$
--   whose final output has strictly positive valuation,
--   $$x\in V(f,a),\qquad \nu(f_{n+1}(x))>0,$$
--   then $f$ is a positive approximate polynomial satisfiability instance.
--
--   Thus a point of the prescribed fiber with positive final valuation is an approximate solution: the first $n$ outputs approach $0$ after cancelling the nonzero constants $a_i$, and the final output also approaches $0$. This is precisely the converse used in the concluding paragraph of Proposition 4; no nonzero assumption on $a$ and no restriction on the characteristic is needed beyond the standing algebraic interfaces.
--
--   **Formalization Note.** `prescribedFiber` uses evaluation in the valued algebraic closure, and `APS f` is Zariski image-closure membership of the origin over $K$.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 4, concluding argument p.20, together with Claim 8 equation (16) p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=20

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.positive_valuation_implies_APS {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : ApproxPolySatCH.Main.MinimallyDependent f) (H : Poly k (n + 1))
    (hH : ApproxPolySatCH.Main.AnnihilatorPresentation f H) (v : ApproxPolySatCH.Main.EpsilonValuation k)
    (a : Fin n → ApproxPolySatCH.Main.Constants k) :
    (∃ x ∈ ApproxPolySatCH.Main.prescribedFiber f a, 0 < v.val (ApproxPolySatCH.Main.evaluateValued (f (Fin.last n)) x)) → ApproxPolySatCH.Main.APS f := by sorry
