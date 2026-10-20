-- Prove2me | Theorems.Thm_DerivativeChainPrivate_nonreal_roots_of_real_polynomial
-- name    : DerivativeChainPrivate.nonreal_roots_of_real_polynomial
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:48:42.357879+00:00
-- url     : https://prove2.me/theorems/e684eeb0-15fd-4da8-a70b-004f2c3ffc79
-- title:
--   Nonreal complex roots equal the real-root defect
-- statement:
--   Let $p$ be a real polynomial. For $p\ne0$, let $N_{\mathbb R}(p)$ count its real roots with multiplicity and let $N_{\mathrm{nr}}(p)$ count the nonreal roots of its complexification, also with multiplicity. Then
--
--   $$N_{\mathrm{nr}}(p)=\deg p-N_{\mathbb R}(p).$$
--
--   This identity relates the real-root deficit to the number of nonreal root slots.
--
--   **Formalization Note** The formal statement also includes $p=0$. Mathlib defines the finite roots multiset of the zero polynomial to be empty and its natural degree to be zero; under those conventions both sides are zero. This is not a claim that the zero polynomial's mathematical zero set is empty. Subtraction is natural-number subtraction. Nonzero constants have no root slots and degree zero.
-- source:
--   Derivative-zero chains: public formalization reference, R29, DerivativeChainPrivate.nonreal_roots_of_real_polynomial. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.nonreal_roots_of_real_polynomial (p : Polynomial ℝ) :
    ((p.map Complex.ofRealHom).roots.filter (fun z => z.im ≠ 0)).card =
      p.natDegree - p.roots.card := by sorry
