-- Prove2me | Theorems.Thm_BSLambda_Final_exists_ratio_blowup
-- name    : BSLambda.Final.exists_ratio_blowup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:51.42881+00:00
-- url     : https://prove2.me/theorems/6f826089-bce6-401d-b255-544957175b04
-- title:
--   Final: exists ratio blowup
-- statement:
--   **`bs` is not `O(lambda²)`** (Section 14).  There is a function `f` whose `m`-fold
--   self-compositions satisfy `bs(F_m) / lambda(F_m)^2 ≥ (14011/U)^m` with `14011/U > 1.768`,
--   so the ratio tends to infinity.  Unlike in Section 14, the multiplicativity of `lambda`
--   under composition is not imported but proved (`BSLambda.lam_iterFun_eq`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L316-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L316-L321

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}

theorem BSLambda.Final.exists_ratio_blowup :
    ∃ γ : Idx → Idx → Fin r, ∀ m : ℕ,
      (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
        ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by sorry
