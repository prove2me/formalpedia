-- Prove2me | Theorems.Thm_FairSelling_descent
-- name    : FairSelling.descent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:00.012836+00:00
-- url     : https://prove2.me/theorems/3f9ee40a-1b33-4bb7-9c6b-cf602dec8cea
-- title:
--   Fair Selling: descent
-- statement:
--   **The descent.**  See the module documentation for the meaning of the configuration.  The
--   conclusion is that a canonical `k`-partition of the available resources exists.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L195-L628
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L195-L628

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem FairSelling.descent (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    (Sset : Finset G) (D : ℝ) (hD : 0 ≤ D)
    (hSwp : ∀ g ∈ Sset, w g ≤ p g)
    (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (hbS : ∀ j, Disjoint Sset (bg j))
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε) :
    ∀ (M : ℕ) (R : Finset G) (J : Finset ι) (Q : Finset κ) (k n₂ : ℕ),
      J.card = M →
      Sset ⊆ R →
      (∀ g ∈ R, vbar w p g ≤ 2 * ε) →
      (∀ b ∈ Q, wit b ∈ bg (bidx b)) →
      (∀ b ∈ Q, cred b ≤ 3 * ε) →
      (∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε) →
      (∀ b ∈ Q, wit b ∉ R) →
      Set.InjOn wit ↑Q →
      (∀ b ∈ Q, bidx b ∈ J) →
      k + n₂ + Q.card = J.card →
      ((J.card : ℝ) * (3 * ε)
        ≤ (∑ j ∈ J, vbarSum w p (bg j ∩ R)) + (∑ g ∈ Sset, p g) + D
            + (n₂ : ℝ) * (2 * ε) + ∑ b ∈ Q, cred b) →
      CanonExists w p (3 * ε) (2 * ε) k R D := by sorry
