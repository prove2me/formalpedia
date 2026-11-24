-- Prove2me | Theorems.Thm_FairSelling_servable_extend_set
-- name    : FairSelling.servable_extend_set
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:20.177088+00:00
-- url     : https://prove2.me/theorems/b2c4af1a-095d-4e33-8300-813e95e0d7b6
-- title:
--   Fair Selling: servable extend set
-- statement:
--   Serving all the agents of `Kset` with the bundles `bundle k` and the money `cash k`, the
--   money being raised from the bank `D` and from force-selling the goods `F`, and then serving the
--   remaining agents out of what is left.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L65-L150
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L65-L150

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.servable_extend_set (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (Kset : Finset (Fin n)) (hKT : Kset ⊆ T)
    (bundle : Fin n → Finset G) (F : Finset G) (cash : Fin n → ℝ)
    (hb : ∀ k ∈ Kset, bundle k ⊆ R) (hF : F ⊆ R)
    (hbdisj : ∀ k ∈ Kset, ∀ l ∈ Kset, k ≠ l → Disjoint (bundle k) (bundle l))
    (hbF : ∀ k ∈ Kset, Disjoint F (bundle k))
    (hcash0 : ∀ k ∈ Kset, 0 ≤ cash k)
    (hserve : ∀ k ∈ Kset, τ k ≤ vbarSum (v k) p (bundle k) + cash k)
    (hrec : Servable v p τ (T \ Kset) (R \ (Kset.biUnion bundle ∪ F))
              (D + (∑ g ∈ F, p g) - ∑ k ∈ Kset, cash k)) :
    Servable v p τ T R D := by sorry
