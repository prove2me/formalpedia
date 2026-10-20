-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exterior_cubic_graph_no_contact
-- name    : DerivativeChainPrivate.exterior_cubic_graph_no_contact
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T11:12:32.897289+00:00
-- url     : https://prove2.me/theorems/ae918ab9-e3d3-4c6f-8f51-83efc26b8121
-- title:
--   Cubic inverse graphs with strict exterior gaps have no northeast boundary contact
-- statement:
--   Supporting boundary-exclusion theorem. At complex points w,z and remainder values e0,e1, compare alpha0*w^3-b0*w+e0 and alpha1*z^3-b1*z+e1. Assume Re w>0, Im w>0, alpha0>alpha1>0, the source real value is nonnegative, A0>=0, A1<=M, C0<=K, C1>=0, M<b1-(alpha1/alpha0)b0 and K<b0-b1, where Aj=Re(ej)/Re(pointj) and Cj=(3Aj-Im(ej)/Im(pointj))/2. If z lies on the vertical or horizontal boundary northeast of w, these graph values are unequal. No analytic branch, remainder bound, root-count persistence, or root existence is asserted.
-- source:
--   Derivative-zero chains: public formalization reference, R56, DerivativeChainPrivate.exterior_cubic_graph_no_contact. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.exterior_cubic_graph_no_contact (w z e₀ e₁ : ℂ)
    (α₀ α₁ b₀ b₁ M K : ℝ)
    (hwre : 0 < w.re) (hwim : 0 < w.im)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀)
    (hsource : 0 ≤ ((α₀ : ℂ) * w ^ 3 - (b₀ : ℂ) * w + e₀).re)
    (hA₀ : 0 ≤ e₀.re / w.re) (hA₁ : e₁.re / z.re ≤ M)
    (hC₀ : (3 * (e₀.re / w.re) - e₀.im / w.im) / 2 ≤ K)
    (hC₁ : 0 ≤ (3 * (e₁.re / z.re) - e₁.im / z.im) / 2)
    (hvertical : M < b₁ - (α₁ / α₀) * b₀)
    (hhorizontal : K < b₀ - b₁)
    (hboundary : (z.re = w.re ∧ w.im ≤ z.im) ∨ (w.re ≤ z.re ∧ z.im = w.im)) :
    (α₀ : ℂ) * w ^ 3 - (b₀ : ℂ) * w + e₀ ≠
      (α₁ : ℂ) * z ^ 3 - (b₁ : ℂ) * z + e₁ := by sorry
