-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_dense_sparse_reductions
-- name    : ApproxPolySatCH.Main.dense_sparse_reductions
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:28.6141+00:00
-- url     : https://prove2.me/theorems/c8437f08-959b-45c8-8add-71bd1a44b77f
-- title:
--   Dense and sparse APS encodings are polynomial-time equivalent
-- statement:
--   For every rational or presented finite coefficient field $k$, the dense-array and sparse-list versions of approximate polynomial satisfiability are polynomial-time many-one equivalent:
--   $$\mathrm{APS}^{\mathrm{dense}}_k\le_m^P\mathrm{APS}^{\mathrm{sparse}}_k,
--   \qquad
--   \mathrm{APS}^{\mathrm{sparse}}_k\le_m^P\mathrm{APS}^{\mathrm{dense}}_k.$$
--
--   The reductions act on the actual binary encodings and preserve validity and the image-closure acceptance condition. Sparse exponents are binary, so the second assertion uses the same circuit-based degree-control mechanism as Proposition 6 rather than assuming that expanding a high-degree monomial into a dense array is polynomial time. Empty, constant and zero systems are included.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §3, paragraph preceding Proposition 6, p.14 (circuit, sparse and dense versions are polynomial-time equivalent), and Proposition 6, pp.14–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=14

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- The two directions of the dense/sparse encoding equivalence for APS. -/
theorem dense_sparse_reductions (k : CoefficientField) :
    ManyOneReduction (DenseLanguage k) (SparseLanguage k) ∧
    ManyOneReduction (SparseLanguage k) (DenseLanguage k) := by sorry
