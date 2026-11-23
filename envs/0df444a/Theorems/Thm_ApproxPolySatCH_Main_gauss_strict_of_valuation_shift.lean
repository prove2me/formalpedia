-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_gauss_strict_of_valuation_shift
-- name    : ApproxPolySatCH.Main.gauss_strict_of_valuation_shift
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:27.653711+00:00
-- url     : https://prove2.me/theorems/6c5bfdd2-5bfe-4987-a84a-fc4a06cc3ae7
-- title:
--   Strict Gauss-valuation test under a low-band valuation shift
-- statement:
--   Let $\nu$ be an epsilon-adic valuation and let $q,r\in L[Z]$, with $q\ne0$ and $D,N\in\mathbb N$. Assume that every nonzero coefficient of $q$ has valuation at most $D$, that on the support of $q$ the coefficients of $r$ satisfy
--   $$\nu(r_i)=\nu(q_i)+N,$$
--   and that whenever $q_i=0$ one has $\nu(r_i)>N+D$.
--
--   Then
--   $$\nu(q)<\nu(q(0))\quad\Longleftrightarrow\quad \nu(r)<\nu(r(0)),$$
--   where $\nu(q)$ and $\nu(r)$ denote Gauss valuations, namely the minima of the valuations of their coefficients.
--
--   This is the finite-support valuation argument underlying the final chain of equivalences in Lemma 12. The uniform bound makes the Gauss valuation of $r$ exactly $N$ plus that of $q$, while the same shift relates their constant coefficients whenever $q(0)\ne0$. Zero coefficients and infinite valuations are included explicitly.
--
--   **Formalization Note.** Coefficients outside the finite support of $r$ have value zero and valuation $\infty$, so no separate support inclusion is required.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), final displayed equivalence in the proof of Lemma 12, p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=22

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.gauss_strict_of_valuation_shift {k : Type} [Field k] (v : EpsilonValuation k)
    (q r : Polynomial (ValuedClosure k)) (D N : ℕ) (hq : q ≠ 0)
    (hbound : ∀ i, q.coeff i ≠ 0 → v.val (q.coeff i) ≤ (D : WithTop ℚ))
    (hmatch : ∀ i, q.coeff i ≠ 0 →
      v.val (r.coeff i) = v.val (q.coeff i) + (N : WithTop ℚ))
    (htail : ∀ i, q.coeff i = 0 →
      ((N + D : ℕ) : WithTop ℚ) < v.val (r.coeff i)) :
    gaussValuation v q < v.val (q.eval 0) ↔
      gaussValuation v r < v.val (r.eval 0) := by sorry
