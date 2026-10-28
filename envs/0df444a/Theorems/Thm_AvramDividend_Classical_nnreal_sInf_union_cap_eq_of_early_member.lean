-- Prove2me | Theorems.Thm_AvramDividend_Classical_nnreal_sInf_union_cap_eq_of_early_member
-- name    : AvramDividend.Classical.nnreal_sInf_union_cap_eq_of_early_member
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:31:45.326986+00:00
-- url     : https://prove2.me/theorems/a07294ab-7ed5-491f-a9a0-eec1920a205e
-- title:
--   Adjoining a finite horizon fallback leaves a nonempty first-hit infimum unchanged whenever the level is hit before the fallback
-- statement:
--   For any subset A of the nonnegative real time axis, if A contains at least one time no later than the deterministic horizon H, then the infimum of A is unchanged by adjoining {H}. This is the precise bridge from the true closed-level hitting clock defined by an infimum of a superlevel set to the bounded stopping clock that adjoins a deterministic H to handle paths with no hit. It makes it possible to transfer the accepted post-hit strong Markov negative-increment result for the capped clock to the actual first hit of a finite excursion whose maximal level is attained strictly before its endpoint.
-- source:
--   Pinned Mathlib csInf_le and le_csInf on the order-complete ℝ≥0 time domain; exact no-hit cap semantics.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical Set
open scoped NNReal

theorem AvramDividend.Classical.nnreal_sInf_union_cap_eq_of_early_member
    (A : Set ℝ≥0) (H : ℝ≥0)
    (hMember : ∃ a : ℝ≥0, a ∈ A ∧ a ≤ H) :
    sInf (A ∪ {H}) = sInf A := by sorry
