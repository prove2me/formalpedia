-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_root_defect_derivative
-- name    : DerivativeChainPrivate.real_root_defect_derivative
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:44:11.365537+00:00
-- url     : https://prove2.me/theorems/ca8f8f94-9954-44e6-8855-55a849f4a746
-- title:
--   Multiplicity-aware real-root defect under differentiation
-- statement:
--   For a real polynomial $p$, write $d(p)$ for its natural degree and $N_{\mathbb R}(p)$ for the size of its finite multiset of real roots, counted with multiplicity. Define $\delta(p)=d(p)-N_{\mathbb R}(p)$ using natural-number subtraction. Then
--
--   $$\delta(p')\le\delta(p).$$
--
--   Differentiation cannot increase this real-root deficit.
--
--   **Formalization Note** The formula includes constants and the zero polynomial. Mathlib assigns the zero polynomial natural degree zero and an empty finite roots multiset, so $\delta(0)=0$. The empty multiset is a library convention, not the zero set of the zero polynomial.
-- source:
--   Derivative-zero chains: public formalization reference, R26, DerivativeChainPrivate.real_root_defect_derivative. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.real_root_defect_derivative (p : Polynomial ℝ) :
    p.derivative.natDegree - p.derivative.roots.card ≤
      p.natDegree - p.roots.card := by sorry
