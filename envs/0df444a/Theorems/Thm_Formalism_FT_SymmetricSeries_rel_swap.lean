-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_rel_swap
-- name    : Formalism.FT.SymmetricSeries.rel_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:20.594351+00:00
-- url     : https://prove2.me/theorems/9df92e9f-e08a-4f84-99c0-8f0f9e2380ff
-- title:
--   Symmetric Series: rel swap
-- statement:
--   The Symmetric Series construction uses the rel swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L159-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L159-L176

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}

theorem Formalism.FT.SymmetricSeries.rel_swap {S : Type*} [CommRing S] (e h : ℕ → S) (k : ℕ)
    (H : ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∑ i ∈ range (k + 1), (-1) ^ i * h i * e (k - i) = 0 := by sorry
