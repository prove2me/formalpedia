-- Prove2me | Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_iff_dnf
-- name    : DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:49.839447+00:00
-- url     : https://prove2.me/theorems/0d2af13f-a703-4374-94ce-ef739d5abaa7
-- title:
--   Quantifier Free Formula: holds iff dnf
-- statement:
--   A quantifier-free formula holds exactly when some clause of its disjunctive normal form
--   holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L123-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L123-L125

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}

theorem DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnf (φ : QuantifierFreeFormula T V) (ρ : V → D) :
    φ.Holds I ρ ↔ ∃ c ∈ φ.dnf, c.Holds I ρ := by sorry
