-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_claim_key
-- name    : Formalism.CoboundaryTransfers.claim_key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:51.845135+00:00
-- url     : https://prove2.me/theorems/56d359dc-492a-4cfe-a7f1-037cd9e9ca98
-- title:
--   Coboundary Transfers: claim key
-- statement:
--   The Coboundary Transfers construction uses the claim key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/TorsionKilledCriterionHolds.lean#L106-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/TorsionKilledCriterionHolds.lean#L106-L168

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

theorem Formalism.CoboundaryTransfers.claim_key (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (w : D) (hw : W.QInv w) (j : ℕ) (y z : D) (hyz : W.C1 y z)
    (hj : ((B.p : O) ^ j) • (B.X • w) = W.d1 y z) :
    Polynomial.aeval δ R (cΓ • w) ∈ W.N := by sorry
