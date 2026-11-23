-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_tri_succ
-- name    : Formalism.FT.SymmetricSeries.tri_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:53.47779+00:00
-- url     : https://prove2.me/theorems/ccffd227-b86e-48ce-ae86-beb3a8b95089
-- title:
--   Symmetric Series: tri succ
-- statement:
--   The Symmetric Series construction uses the tri succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L125-L128

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

theorem Formalism.FT.SymmetricSeries.tri_succ (k : ℕ) : tri R n (k + 1) =
    ∑ i ∈ range (k + 1), (-1) ^ i * yv R n (i + 1) * tri R n (k - i) := by sorry
