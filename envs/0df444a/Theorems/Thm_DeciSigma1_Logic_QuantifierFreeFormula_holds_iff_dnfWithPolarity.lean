-- Prove2me | Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_iff_dnfWithPolarity
-- name    : DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnfWithPolarity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:47.712796+00:00
-- url     : https://prove2.me/theorems/735f2469-25c1-42ed-bdc0-c42c08a92f22
-- title:
--   Quantifier Free Formula: holds iff dnf With Polarity
-- statement:
--   The Quantifier Free Formula construction uses the holds iff dnf With Polarity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L98-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L98-L115

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

theorem DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnfWithPolarity (φ : QuantifierFreeFormula T V) (ρ : V → D)
    (b : Bool) :
    (if b then φ.Holds I ρ else ¬ φ.Holds I ρ) ↔ ∃ c ∈ φ.dnfWithPolarity b, c.Holds I ρ := by sorry
