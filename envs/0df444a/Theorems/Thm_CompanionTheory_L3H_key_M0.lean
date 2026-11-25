-- Prove2me | Theorems.Thm_CompanionTheory_L3H_key_M0
-- name    : CompanionTheory.L3H.key_M0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:37.613386+00:00
-- url     : https://prove2.me/theorems/ec339b90-7a9a-4675-b4f5-030245a0d85b
-- title:
--   L3 H: key M0
-- statement:
--   The L3 H construction uses the key M0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L57-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L57-L91

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem CompanionTheory.L3H.key_M0 {l : ℕ} [Fact l.Prime] {c : ℕ} (hc : c ≠ 0) (x : L)
    (hx : ∃ m : ℕ, ¬ l ∣ m ∧ ((m * c ^ 2 : ℕ) : AL L) * (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) ∈ ALint L)
    (τ : L →+* ℂ) : τ x ∈ M0 L l c := by sorry
