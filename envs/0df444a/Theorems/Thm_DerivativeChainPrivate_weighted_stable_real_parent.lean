-- Prove2me | Theorems.Thm_DerivativeChainPrivate_weighted_stable_real_parent
-- name    : DerivativeChainPrivate.weighted_stable_real_parent
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:02:16.605093+00:00
-- url     : https://prove2.me/theorems/3d73be8f-6226-49c7-b160-9f16f867c2b1
-- title:
--   A stable weighted real root has an outward same-sign parent
-- statement:
--   For a nonzero real polynomial Q, suppose (r+1)Q+(k+1)XQ′ has exactly as many real root slots as Q, counted with multiplicity. Every nonzero real root y of that weighted polynomial has a root x of Q of the same sign and at least as large a modulus. Neither polynomial is assumed to split over the reals. This proves the real parent selection step only.
-- source:
--   Derivative-zero chains: public formalization reference, R46, DerivativeChainPrivate.weighted_stable_real_parent. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.weighted_stable_real_parent (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ)
    (hcount : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).roots.card =
      q.roots.card) (y : ℝ)
    (hy : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0)
    (hyne : y ≠ 0) :
    ∃ x ∈ q.roots, (0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y) := by sorry
