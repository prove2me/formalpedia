-- Prove2me | Theorems.Thm_BSLambda_LLL_violSet_cert_eq
-- name    : BSLambda.LLL.violSet_cert_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:21.222925+00:00
-- url     : https://prove2.me/theorems/7fe4f3f4-3261-49b1-94e7-db1d780391a6
-- title:
--   LLL: viol Set cert eq
-- statement:
--   The violated literals of `P_i` split into the zeros of `x` in the owner block and the
--   outgoing gates whose target coordinate `x` fails to zero out.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L260-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L260-L280

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

theorem BSLambda.LLL.violSet_cert_eq (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    (Construction.cert Arc γ i).violSet x =
      (zeroSet x i).image (fun k => ((i, k) : Construction.Coord ι r)) ∪
        (missSet Arc γ (zeroSet x) Finset.univ i).image (Construction.gateCoord γ i) := by sorry
