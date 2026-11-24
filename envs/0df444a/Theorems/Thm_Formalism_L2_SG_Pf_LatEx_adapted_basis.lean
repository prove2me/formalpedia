-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_adapted_basis
-- name    : Formalism.L2.SG.Pf.LatEx.adapted_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:35.584728+00:00
-- url     : https://prove2.me/theorems/c1d957b4-3f25-40dc-a87b-4103c6545773
-- title:
--   Lat Ex: adapted basis
-- statement:
--   The Lat Ex construction uses the adapted basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L224-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L224-L261

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E

theorem Formalism.L2.SG.Pf.LatEx.adapted_basis (n : ℕ) : ∀ (w : Fin (n + 1) → V), LinearIndependent E w →
    ∀ (M : Submodule (𝓞 E) V), M.FG →
    M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) →
    (∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • w i ∈ M) →
    ∀ a : Fin n → 𝓕, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → V) (c : 𝓕), c ≠ 0 ∧
      M = latSpanV (Fin.snoc (α := fun _ => 𝓕) a c) e := by sorry
