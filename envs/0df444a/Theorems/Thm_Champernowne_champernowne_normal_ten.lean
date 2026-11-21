-- Prove2me | Theorems.Thm_Champernowne_champernowne_normal_ten
-- name    : Champernowne.champernowne_normal_ten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:56.409177+00:00
-- url     : https://prove2.me/theorems/b23db8d2-9d22-495f-a90d-f6c198b229d4
-- title:
--   Champernowne: champernowne normal ten
-- statement:
--   The classical base-10 statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Main.lean#L27-L28
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Main.lean#L27-L28

module
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Definitions.Def_LeanPool_Champernowne_Main
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champernowne_normal_ten : IsNormalSequence 10 (champDigit 10) := by sorry
