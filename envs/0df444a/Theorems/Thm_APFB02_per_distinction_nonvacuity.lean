-- Prove2me | Theorems.Thm_APFB02_per_distinction_nonvacuity
-- name    : APFB02.per_distinction_nonvacuity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T15:27:21.835029+00:00
-- url     : https://prove2.me/theorems/d2a73d60-6aa6-40c9-bc2d-bc36c5ba0f6e
-- title:
--   Under B02 every distinction separates two inputs with different continuation profiles and has a realizing protocol
-- statement:
--   ### What this establishes
--
--   Assume the declared **B02 distinction input**. In every context, each physical distinction separates two raw inputs whose continuation profiles differ. A protocol realizes the distinction using a maintained, sufficient record set.
--
--   ### Why it follows
--
--   B02 already supplies separation and realization. If the two continuation profiles were equal, B02's descent clause would force equal distinction values, contradicting separation.
--
--   ### Scope
--
--   The continuation profile remains a parameter. This result makes no claim about costs, capacity, a prepared input, or observed execution.
--
--   **Foundation Inputs:** revision 2026-10-04.1. **Input consumed:** B02. No new definition or physical premise is added.
-- source:
--   Paper 1 Technical Supplement v9.28, 1059 (physical distinction), 2158–2164 (continuation separation); FOUNDATION_INPUTS.json revision 2026-10-04.1. Source module Theorems.Thm_APFB02_per_distinction_nonvacuity; SHA256 03286728e3074921032c89e370dee314a72f3909557d62278bfe67e9f3dc4007.

import Definitions.Def_APF_B02_DeclaredInput
set_option autoImplicit false
universe uG uX uQ uP uR
open APFB02

theorem APFB02.per_distinction_nonvacuity
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : B02SourceMeaning Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    ∃ x y : X g, d.val x ≠ d.val y ∧ Cont g x ≠ Cont g y ∧
      ∃ (p : P g) (sigma : Record g → Prop),
        (∀ r, sigma r → maintained g p r) ∧
        sufficient g p sigma d ∧ usesToRealize g p d sigma := by sorry
