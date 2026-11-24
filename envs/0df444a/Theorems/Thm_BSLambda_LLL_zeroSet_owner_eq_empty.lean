-- Prove2me | Theorems.Thm_BSLambda_LLL_zeroSet_owner_eq_empty
-- name    : BSLambda.LLL.zeroSet_owner_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:19.792382+00:00
-- url     : https://prove2.me/theorems/95868949-a641-410b-affd-961bfd742c8f
-- title:
--   LLL: zero Set owner eq empty
-- statement:
--   The zero set of a point of `C_h` in the owner's own block is empty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L229-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L229-L234

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

theorem BSLambda.LLL.zeroSet_owner_eq_empty {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {h : ι}
    {x : Input (Construction.Coord ι r)} (hx : (Construction.cert Arc γ h).Sat x) :
    zeroSet x h = ∅ := by sorry
