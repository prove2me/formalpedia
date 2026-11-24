-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_map_bidet
-- name    : Formalism.L2.DIV.fk_map_bidet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:41.422329+00:00
-- url     : https://prove2.me/theorems/fe68bcee-eb97-4dad-8831-a3174ecb6918
-- title:
--   DIV: fk map bidet
-- statement:
--   The DIV construction uses the fk map bidet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkMapInitMinor.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkMapInitMinor.lean#L20-L25

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions

theorem Formalism.L2.DIV.fk_map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n k : ℕ} (sz : Fin k → ℕ)
    (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r) :
    map φ (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant S sz hsz I := by sorry
