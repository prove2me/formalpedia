-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_offDiag_of_card_inter_le_one
-- name    : BSLambda.LLL.disjoint_offDiag_of_card_inter_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:30.444984+00:00
-- url     : https://prove2.me/theorems/a4c3da6f-509a-4051-b7d3-93e5a32fa058
-- title:
--   LLL: disjoint off Diag of card inter le one
-- statement:
--   Supports meeting in at most one vertex share no arc variable (Section 7).  This is what
--   makes the dependency graph of Section 10 — adjacency iff the supports share at least two
--   vertices — a valid one.
--
--   The variables of a support `S` are its *off-diagonal* pairs: no event ever reads a loop
--   variable `ω (v, v)`, since every arc is irreflexive and every conditioned owner gate `(h, j)`
--   has `j` a non-owner, and leaving the diagonal out is exactly what makes this true.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L68-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L68-L73

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]

theorem BSLambda.LLL.disjoint_offDiag_of_card_inter_le_one {S T : Finset ι} (h : (S ∩ T).card ≤ 1) :
    Disjoint S.offDiag T.offDiag := by sorry
