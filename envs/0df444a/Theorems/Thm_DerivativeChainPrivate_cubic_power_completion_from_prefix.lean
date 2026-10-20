-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_power_completion_from_prefix
-- name    : DerivativeChainPrivate.cubic_power_completion_from_prefix
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T11:10:48.310974+00:00
-- url     : https://prove2.me/theorems/fdad4af8-eb46-4766-a855-55d5e43de125
-- title:
--   A northeast actual prefix completes a cubic power with length at most four sqrt two radii over three
-- statement:
--   Supporting completion theorem, with the analytic existence premise explicit. Let h>0, q=(X-u)(X-v)(X-w), and let u,v,w lie in a disk of radius R centered at o. Given an actual derivative-root prefix f through rows 1..2h, starting at the cubic centroid, with both coordinates nondecreasing, and with u northeast of its endpoint, there exists a complete actual chain for q^h of cost at most 4 sqrt(2) R/3. It agrees with the prefix and repeats u on the final h rows. Repeated source roots and zero radius are allowed. The theorem does not construct the required prefix or northeast source root, so does not prove the unconditional cube or fourth-power result.
-- source:
--   Derivative-zero chains: public formalization reference, R55, DerivativeChainPrivate.cubic_power_completion_from_prefix. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.cubic_power_completion_from_prefix (q : Polynomial ℂ) (h : ℕ) (hh : 0 < h)
    (u v w o : ℂ) (R : ℝ)
    (hq : q = (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) *
      (Polynomial.X - Polynomial.C w))
    (hu : ‖u - o‖ ≤ R) (hv : ‖v - o‖ ≤ R) (hw : ‖w - o‖ ≤ R)
    (f : ℕ → ℂ) (hfirst : f 0 = (u + v + w) / 3)
    (hroot : ∀ i < 2 * h,
      (Polynomial.derivative^[3 * h - (i + 1)] (q ^ h)).eval (f i) = 0)
    (hre : ∀ i < 2 * h - 1, (f i).re ≤ (f (i + 1)).re)
    (him : ∀ i < 2 * h - 1, (f i).im ≤ (f (i + 1)).im)
    (hjoinre : (f (2 * h - 1)).re ≤ u.re)
    (hjoinim : (f (2 * h - 1)).im ≤ u.im) :
    ∃ z : Fin (3 * h) → ℂ,
      (∀ i, (Polynomial.derivative^[3 * h - (i.val + 1)] (q ^ h)).eval (z i) = 0) ∧
      chainCost z ≤ 4 * Real.sqrt 2 * R / 3 ∧
      (∀ i, i.val < 2 * h → z i = f i.val) ∧
      (∀ i, 2 * h ≤ i.val → z i = u) := by sorry
