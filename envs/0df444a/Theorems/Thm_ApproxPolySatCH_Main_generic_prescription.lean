-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_generic_prescription
-- name    : ApproxPolySatCH.Main.generic_prescription
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:15.677834+00:00
-- url     : https://prove2.me/theorems/8e122a56-3055-4e31-88f5-3d2949cbbf5e
-- title:
--   Proposition 4 — Generic finite nonempty prescription
-- statement:
--   Let $f=(f_1,\ldots,f_{n+1})$ be minimally dependent in $n\ge1$ variables over $k$, and let $\nu$ be an epsilon-adic valuation on $L$. Put
--   $$\Delta=\max_i\deg f_i,\qquad\Delta_{\mathrm{bad}}=\Delta^{n+1}+n\Delta^n.$$
--   There are one nonzero $Q_{\mathrm{bad}}\in k[Y_1,\ldots,Y_n]$ of degree at most $\Delta_{\mathrm{bad}}-1$ and one coordinate permutation, both independent of a, such that for every $a\in\overline k^n$ outside its zero set the prescribed fiber is finite and nonempty, and
--   $$\mathrm{APS}(f)\iff\exists x\in V(f,a):\nu(f_{n+1}(x))>0.$$
--   The displayed fiber and final coordinate use the permuted tuple.
--
--   This gives the full generic prescription and explicit exceptional-locus degree bound.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: A single Qbad and permutation, followed by every parameter outside the exceptional locus. → Finite indices with one permutation and one Q chosen before a; the fiber is a set in the valued algebraic closure.; reason: This preserves both finiteness and nonemptiness and both directions of the APS equivalence.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 4, p.18 (PDF p.18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=18

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem generic_prescription {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f) (v : EpsilonValuation k) :
    ∃ (Q : Poly k n) (sigma : Equiv.Perm (Fin (n + 1))), Q ≠ 0 ∧
      Q.totalDegree ≤ maxDegree f ^ (n + 1) + n * maxDegree f ^ n - 1 ∧
      ∀ a : Fin n → Constants k, MvPolynomial.eval₂ (algebraMap k (Constants k)) a Q ≠ 0 →
        (prescribedFiber (fun i => f (sigma i)) a).Finite ∧
        (prescribedFiber (fun i => f (sigma i)) a).Nonempty ∧
        (APS f ↔ ∃ x ∈ prescribedFiber (fun i => f (sigma i)) a,
          0 < v.val (evaluateValued (f (sigma (Fin.last n))) x)) := by sorry

end ApproxPolySatCH.Main
