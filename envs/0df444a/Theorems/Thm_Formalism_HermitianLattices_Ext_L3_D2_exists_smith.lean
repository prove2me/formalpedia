-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_smith
-- name    : Formalism.HermitianLattices.Ext.L3.D2.exists_smith
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:05.455884+00:00
-- url     : https://prove2.me/theorems/8155a149-ad18-4945-85aa-aee96e69d6e6
-- title:
--   D2: exists smith
-- statement:
--   The D2 construction uses the exists smith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L14-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L14-L140

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open LocalSpans

theorem Formalism.HermitianLattices.Ext.L3.D2.exists_smith {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (a b : Basis (Fin (finrank K V)) K V) (e : Fin (finrank K V) → 𝓞 K) (c : 𝓞 K),
      c ≠ 0 ∧ (∀ i, e i ≠ 0) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀ ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 B₀ ∧ ∀ i, c • b i = e i • a i := by sorry
