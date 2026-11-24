-- Prove2me | Theorems.Thm_BSLambda_LLL_sum_branch_pow_eq
-- name    : BSLambda.LLL.sum_branch_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:41.786385+00:00
-- url     : https://prove2.me/theorems/b91c3b1b-ef7e-4265-a7f9-491ab8f26440
-- title:
--   LLL: sum branch pow eq
-- statement:
--   **Section 9**: evaluating the triple sum of the branch bounds: collapse the two inner
--   constant sums, then regroup the outer powerset sum by cardinality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1110-L1147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1110-L1147

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

theorem BSLambda.LLL.sum_branch_pow_eq [NeZero r] {S : Finset ι} {h : ι} (hh : h ∈ S) (hS : S.card = 9)
    {AA : Finset (ι × ι)} (hAA : AA.card = 28) :
    ∑ L ∈ (S.erase h).powerset, ∑ _w ∈ (L.pi fun _ => (Finset.univ : Finset (Fin r))),
        ∑ _X ∈ AA.powersetCard (8 - L.card), ((2 : ℝ) / r) ^ (AA.card - (8 - L.card))
      = (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by sorry
