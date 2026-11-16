-- Prove2me | Theorems.Thm_APFB02_per_distinction_nonvacuity_r3
-- name    : APFB02.per_distinction_nonvacuity_r3
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:51:49.929195+00:00
-- url     : https://prove2.me/theorems/fcdfaaa8-9e19-42a3-8c3f-dc2f0a8bbd20
-- title:
--   Separator and protocol witnesses extracted from proposed r3
-- statement:
--   Assuming the proposed whole r3 statement, each domain distinction has states with different readings and profiles, and a protocol with a maintained sufficient record set used to realize that distinction.
--
--   Publication scope: The proof uses the old separator conjunct, but the stated hypothesis is the full proposed r3 form. This theorem does not adopt that form or establish an original physical instance.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB02_per_distinction_nonvacuity_r3.lean:27 (source SHA256 590a15eee98c2293a94c464a9d3f998da6a1ae985b21ce6a4dc071b909036ccb; APFB02.per_distinction_nonvacuity_r3)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB02_per_distinction_nonvacuity_r3].declarations[APFB02.per_distinction_nonvacuity_r3])']

import Definitions.Def_APF_B02_DeclaredInput_r3_whole_proposed

set_option autoImplicit false

universe uG uX uQ uP uR

namespace APFB02
end APFB02
open APFB02

theorem APFB02.per_distinction_nonvacuity_r3
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : B02SourceMeaning_r3_whole Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    ∃ x y : X g, d.val x ≠ d.val y ∧ Cont g x ≠ Cont g y ∧
      ∃ (p : P g) (sigma : Record g → Prop),
        (∀ r, sigma r → maintained g p r) ∧
        sufficient g p sigma d ∧ usesToRealize g p d sigma := by sorry
