-- Prove2me | Theorems.Thm_BSLambda_LLL_dist_cert_eq
-- name    : BSLambda.LLL.dist_cert_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:23.774148+00:00
-- url     : https://prove2.me/theorems/095f0670-b0e5-41f3-a31e-277be327c60d
-- title:
--   LLL: dist cert eq
-- statement:
--   The distance from `x` to `C_i` counts the zeros of `x` in block `i` together with the
--   gates out of `i` that miss their target zero set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L296-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L296-L303

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

theorem BSLambda.LLL.dist_cert_eq (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    (Construction.cert Arc γ i).dist x =
      (zeroSet x i).card + (missSet Arc γ (zeroSet x) Finset.univ i).card := by sorry
