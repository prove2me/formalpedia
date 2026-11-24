-- Prove2me | Theorems.Thm_BSLambda_CertFamily_ne_of_dist_eq_one
-- name    : BSLambda.CertFamily.ne_of_dist_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:28.07601+00:00
-- url     : https://prove2.me/theorems/9201fef2-766c-4245-af37-afd9433935c7
-- title:
--   Cert Family: ne of dist eq one
-- statement:
--   A point at distance one from another point's certificate is not that point, since every
--   point satisfies its own certificate.  This is why the oriented lemmas below take no
--   separate `x ≠ y` hypothesis (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L119-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L119-L122

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)

theorem BSLambda.CertFamily.ne_of_dist_eq_one {x y : Ones F.ind} (hd : (F.P (F.owner y)).dist x.1 = 1) : x ≠ y := by sorry
