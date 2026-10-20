-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_root_defect_iterate
-- name    : DerivativeChainPrivate.real_root_defect_iterate
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:47:20.452155+00:00
-- url     : https://prove2.me/theorems/edd8ed3f-434a-407b-9baf-5c37d7bbe7a4
-- title:
--   Real-root defect throughout an iterated derivative tower
-- statement:
--   For every real polynomial $p$ and integer $k\ge0$, write $d(p)$ for its natural degree and $N_{\mathbb R}(p)$ for the size of its finite real-root multiset, counting multiplicity. With natural-number subtraction, let $\delta(p)=d(p)-N_{\mathbb R}(p)$. Then
--
--   $$\delta\bigl(p^{(k)}\bigr)\le\delta(p).$$
--
--   The bound holds for every differentiation order, including orders that give the zero polynomial.
--
--   **Formalization Note** Mathlib gives the zero polynomial natural degree zero and an empty finite roots multiset. Thus $\delta(0)=0$ by convention; its mathematical zero set is not empty.
-- source:
--   Derivative-zero chains: public formalization reference, R27, DerivativeChainPrivate.real_root_defect_iterate. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Theorems.Thm_DerivativeChainPrivate_real_root_defect_derivative

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.real_root_defect_iterate (p : Polynomial ℝ) (k : ℕ) :
    ((Polynomial.derivative^[k]) p).natDegree -
        ((Polynomial.derivative^[k]) p).roots.card ≤ p.natDegree - p.roots.card := by sorry
