-- Prove2me | Theorems.Thm_Champernowne_cohort_le_n
-- name    : Champernowne.cohort_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:16.883079+00:00
-- url     : https://prove2.me/theorems/8e48bf95-010f-40fc-8dda-45f399cd76b3
-- title:
--   Champernowne: cohort le n
-- statement:
--   Length lower bound: `n` dominates the second-to-top cohort.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L41-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L41-L67

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology

theorem Champernowne.cohort_le_n {b : ℕ} (hb : 1 < b) (n : ℕ) :
    (b - 1) * b ^ (champM b n - 2) * (champM b n - 1) ≤ n := by sorry
