-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_map_comap_of_inert
-- name    : Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.map_comap_of_inert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:30.042777+00:00
-- url     : https://prove2.me/theorems/61155314-603f-4538-b821-e2797326ecbd
-- title:
--   Split Prime Ideals: map comap of inert
-- statement:
--   The Split Prime Ideals construction uses the map comap of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSubMemOfInert.lean#L123-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSubMemOfInert.lean#L123-L161

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.map_comap_of_inert (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    (P.comap ι).map ι = P := by sorry
