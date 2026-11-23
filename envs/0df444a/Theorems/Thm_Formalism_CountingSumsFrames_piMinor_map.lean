-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_piMinor_map
-- name    : Formalism.CountingSumsFrames.piMinor_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:56.760697+00:00
-- url     : https://prove2.me/theorems/afacdf59-4c05-41cc-a17c-669103a42e71
-- title:
--   Counting Sums Frames: pi Minor map
-- statement:
--   The Counting Sums Frames construction uses the pi Minor map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ExistsNonzeroExchangedMinorHolds.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ExistsNonzeroExchangedMinorHolds.lean#L17-L38

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.piMinor_map {p r k : ℕ} [Fact p.Prime] {F A : Type} [Field F] [CharP F p] [CommRing A] [Algebra F A]
    [Nontrivial A] (H : Matrix (Fin r) (Fin k) F) (pos : Fin r → ℕ) (t : Fin r → Fin r → A) (zj : ℕ)
    (cols : Fin r → Fin k) (hpos : ∀ l, pos l ≤ zj) :
    piMinor p r k (H.map (algebraMap F A)) pos t zj cols =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)).det *
        algebraMap F A ((H.submatrix id cols).det ^ p ^ zj) := by sorry
