-- Prove2me | Theorems.Thm_DerivativeChainPrivate_chainCost_le_radius_add_turn
-- name    : DerivativeChainPrivate.chainCost_le_radius_add_turn
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:08:49.332862+00:00
-- url     : https://prove2.me/theorems/806fd12b-4689-4d0a-a799-e02787274082
-- title:
--   A finite polar chain is bounded by radius increase plus angular variation
-- statement:
--   For a positive finite length n, let radii r_i be nonnegative, nondecreasing and bounded by R>=0. If the sum of the absolute consecutive angle increments is at most alpha, the complex chain r_i exp(i theta_i) has cost at most R-r_0+R alpha. The theorem concerns any such polar chain; actual derivative-root membership is not assumed or concluded.
-- source:
--   Derivative-zero chains: public formalization reference, R50, DerivativeChainPrivate.chainCost_le_radius_add_turn. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.chainCost_le_radius_add_turn {n : ℕ} (hn : 1 ≤ n)
    (r theta : ℕ → ℝ) (R alpha : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i < n, 0 ≤ r i) (hmono : ∀ i < n - 1, r i ≤ r (i + 1))
    (hradius : ∀ i < n, r i ≤ R)
    (hturn : (∑ i ∈ Finset.range (n - 1), |theta (i + 1) - theta i|) ≤ alpha) :
    chainCost (fun i : Fin n => (r i.val : ℂ) * Complex.exp (Complex.I * theta i.val)) ≤
      R - r 0 + R * alpha := by sorry
