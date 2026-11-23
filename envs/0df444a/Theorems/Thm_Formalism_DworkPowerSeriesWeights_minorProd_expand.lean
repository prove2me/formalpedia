-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_expand
-- name    : Formalism.DworkPowerSeriesWeights.minorProd_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:07.362665+00:00
-- url     : https://prove2.me/theorems/d760d87b-b5e9-48cf-8afc-ef59636f20bb
-- title:
--   Dwork Power Series Weights: minor Prod expand
-- statement:
--   The Dwork Power Series Weights construction uses the minor Prod expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L21-L36

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.minorProd_expand {R : Type} [CommRing R] {ι : Type} {N0 N1 Cn : ℕ}
    (x : Fin N0 → Fin N0 → R) (Y : Fin N0 → Fin N1 → MvPolynomial ι R) (p : Fin Cn → ℕ)
    (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    minorProd (fun i b => ∑ a, C (x i a) * Y a b) p hp I =
      ∑ A ∈ Fintype.piFinset (fun c => (Finset.univ : Finset (Fin (p c) → Fin N0))),
        (∏ c, ∏ r', Y (A c r') (I c r')) *
          C (∏ c, (Matrix.of fun (r r' : Fin (p c)) =>
            x ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (A c r')).det) := by sorry
