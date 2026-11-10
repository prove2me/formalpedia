-- Prove2me | Theorems.Thm_APSCounting893_Main_zero_fiber_residues
-- name    : APSCounting893.Main.zero_fiber_residues
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:18.310492+00:00
-- url     : https://prove2.me/theorems/f4260bf3-1bee-4a08-bb32-de432860feb7
-- title:
--   Proposition 4.5 — All and only the residues in the zero fiber
-- statement:
--   Let $Z$ be the actual Puiseux solution set of $y_i=f_i(x)$ and $\pi(y)=t\alpha$ in the admissible reduced-map and line setup. Let $Y_0=Y\cap\pi^{-1}(0)$. Then
--
--   $$\forall(x,y)\in Z,\quad\operatorname{ord}_t(y_i)\ge0\ (\text{all }i),\quad y(0)\in Y_0,$$
--   $$\forall y_0\in Y_0,\quad\exists(x,y)\in Z,\quad y(0)=y_0.$$
--
--   Only output coordinates must have nonnegative valuation. Input coordinates may diverge. The second displayed assertion is residue coverage, not just containment of an arbitrarily supplied list.
--
--   Differences from the source:
--   - encoding: Puiseux tuples and specialization at t=0 → Hahn-series tuples belonging to the entire ramified union, with residue equal to coefficient zero; reason: preserves the valuation of zero and allows negative input valuations
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Proposition 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem zero_fiber_residues (F : ReducedMap) (D : LineData F) :
    (∀ z ∈ lineSolutions F D,
      (∀ j : Fin (F.n + 1), PuiseuxIntegral (z (j.natAdd F.n))) ∧
        outputResidue F z ∈ zeroFiber F D.c) ∧
    (∀ y ∈ zeroFiber F D.c, ∃ z ∈ lineSolutions F D, outputResidue F z = y) := by sorry

end APSCounting893.Main
