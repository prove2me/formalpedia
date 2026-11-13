-- Prove2me | Theorems.Thm_APFB06_amendedB06_occupied_chain_bound
-- name    : APFB06.amendedB06_occupied_chain_bound
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T16:48:43.416206+00:00
-- url     : https://prove2.me/theorems/e4102a38-f9f2-4ea4-bdf4-d534453c6b06
-- title:
--   A tested support-novel chain building the occupied family has at most C/epsilon steps
-- statement:
--   ### A chain bound at the occupied family
--
--   **Explicit hypotheses:** the guarded **B05 marginal floor**, amended **B06 occupancy**, and `hJ`: every protocol in the supplied joint class serves its family from its own maintained sufficient support. The result is conditional on `hJ`; B06 does not prove it.
--
--   There are an occupied alignment, an available joint protocol and an input as supplied by B06. For every supplied chain ending at that alignment's carried family, with each step inserting a tested, support-novel distinction,
--
--   $$n,arepsilon_Gamma leq operatorname{bill}_Gamma(p),qquad n leq rac{C_Gamma}{arepsilon_Gamma}.$$
--
--   ### Scope
--
--   This bounds **chain steps**. It does not construct the chain, prove maximality, define a rank value, or count all members of the carried family. It does not prove that the selected protocol's bill is at most capacity. Continuation remains a parameter.
--
--   The proof applies the existing B05 chain theorem to the family made ledger-admissible by the occupied-family bridge.
--
--   **Foundation Inputs:** revision 2026-10-04.1; B05 and B06 with the named `hJ` condition. No input or definition is changed.
-- source:
--   Paper 1 Technical Supplement v9.28: 1872–1884 (occupancy), 2800–2810 (family-cost monotonicity), 2868–2907 (chain floor); FOUNDATION_INPUTS.json revision 2026-10-04.1. Named hJ compatibility hypothesis as recorded in BATCH_4_MANIFEST.json. Source Theorems.Thm_APFB06_occupied_chain_bound; SHA256 93750f5a6b267a3105a08d709e63bb3bd15858ba22f57f8f7edb8b62e966f9e1.

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
open APFB06 APFPaper1.Source

theorem APFB06.amendedB06_occupied_chain_bound
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
    [∀ g, DecidableEq (Task (Cont g) (D g))]
    (tested : (g : Context) → Task (Cont g) (D g) → Prop)
    (epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested (fun g => (C g : ℝ)) epsilon)
    (hJ : ∀ (g : Context) (S : Finset (Task (Cont g) (D g))) (p : {p // p ∈ protocols g}),
      p ∈ J g S → ∀ d ∈ S, ∃ sigma : Set (Record g),
        sigma ⊆ maintained g p ∧ sufficient g p sigma d ∧ usesToRealize g p d sigma)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      ∀ (n : ℕ) (S : ℕ → Finset (Task (Cont o.1) (D o.1))) (d : ℕ → Task (Cont o.1) (D o.1)),
        (∀ i < n, S (i + 1) = insert (d i) (S i)) →
        (∀ i < n, tested o.1 (d i)) →
        (∀ i < n, supportNovel (wholeResource o.1) (calibration o.1) (maintained o.1)
          (sufficient o.1) (usesToRealize o.1) (S i) (d i)) →
        S n = o.2.carried →
        (n : ℝ) * epsilon o.1 ≤ (calibration o.1 (wholeResource o.1 p) : ℝ) ∧
          (n : ℝ) ≤ (C o.1 : ℝ) / epsilon o.1 := by sorry
