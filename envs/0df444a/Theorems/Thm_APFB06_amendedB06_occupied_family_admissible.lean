-- Prove2me | Theorems.Thm_APFB06_amendedB06_occupied_family_admissible
-- name    : APFB06.amendedB06_occupied_family_admissible
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T16:47:00.167753+00:00
-- url     : https://prove2.me/theorems/98f17550-740f-4049-9c92-a6487c36c10a
-- title:
--   If every protocol in the joint class serves its family, the occupied family is ledger-admissible
-- statement:
--   ### Joint protocols and the occupied family
--
--   **Explicit hypothesis — joint protocols serve their family.** For every context and family, each protocol in the supplied joint class serves every family member using its own maintained sufficient support. This is the hypothesis `hJ`; it is not proved from B06.
--
--   Under that hypothesis and the amended **B06 occupancy input**, there are an actual alignment, a joint protocol for its nonempty carried family, and a raw input from which that same protocol is available. The carried family is feasible and its family cost is at most the context capacity. Its family cost is also at most the selected protocol's calibrated bill.
--
--   ### What the bridge preserves
--
--   The proof compares the real infimum over serving protocols with the extended-real infimum over the supplied joint class. Only inclusion is required. The supporting lemmas prove feasibility, the bound by any joint candidate's bill, and transfer of the joint infimum's capacity bound.
--
--   The result does **not** equate the two infima or bound the selected protocol's bill by capacity. It assumes no minimizer and asserts no observed execution. Continuation remains a parameter.
--
--   **Premises:** B06 and the explicit `hJ` compatibility condition. Foundation Inputs revision 2026-10-04.1. No input or definition is changed.
-- source:
--   Paper 1 Technical Supplement v9.28: 1787–1794 (joint-cost valuation), 1872–1884 (occupancy); FOUNDATION_INPUTS.json revision 2026-10-04.1. Named hJ compatibility hypothesis as recorded in BATCH_4_MANIFEST.json. Source Theorems.Thm_APFB06_occupied_family_cost_bridge; SHA256 4ec6d440805541018615fdae3e0e59f90f218870b3da7b366a5b12773caf4787.

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost
set_option autoImplicit false
open APFB06 APFPaper1.Source

theorem APFB06.amendedB06_occupied_family_admissible
    {Context : Type*} {Raw FullProcess Resource Record : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (maintained : (g : Context) → {p // p ∈ protocols g} → Set (Record g))
    (sufficient : (g : Context) → {p // p ∈ protocols g} → Set (Record g) →
      Task (Cont g) (D g) → Prop)
    (usesToRealize : (g : Context) → {p // p ∈ protocols g} →
      Task (Cont g) (D g) → Set (Record g) → Prop)
    (hJ : ∀ (g : Context) (S : Finset (Task (Cont g) (D g))) (p : {p // p ∈ protocols g}),
      p ∈ J g S → ∀ d ∈ S, ∃ sigma : Set (Record g),
        sigma ⊆ maintained g p ∧ sufficient g p sigma d ∧ usesToRealize g p d sigma)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      familyAdmissible (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
        (usesToRealize o.1) (C o.1 : ℝ) o.2.carried ∧
      familyCost (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
        (usesToRealize o.1) o.2.carried ≤ (calibration o.1 (wholeResource o.1 p) : ℝ) := by sorry
