-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_aeval_tri
-- name    : Formalism.FT.SymmetricSeries.aeval_tri
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:43.575335+00:00
-- url     : https://prove2.me/theorems/a8220eb3-a44e-4332-b240-a17b01792059
-- title:
--   Symmetric Series: aeval tri
-- statement:
--   The Symmetric Series construction uses the aeval tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L130-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L130-L157

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

theorem Formalism.FT.SymmetricSeries.aeval_tri {S : Type*} [CommRing S] [Algebra R S] (e h : ℕ → S) (he0 : e 0 = 1)
    (hh0 : h 0 = 1)
    (rel : ∀ k, 1 ≤ k → k ≤ n → ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∀ k, k ≤ n → MvPolynomial.aeval (fun j : Fin n => e (j + 1)) (tri R n k) = h k := by sorry
