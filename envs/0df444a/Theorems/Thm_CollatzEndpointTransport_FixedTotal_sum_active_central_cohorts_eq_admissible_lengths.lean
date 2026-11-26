-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_active_central_cohorts_eq_admissible_lengths
-- name    : CollatzEndpointTransport.FixedTotal.sum_active_central_cohorts_eq_admissible_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:36.846536+00:00
-- url     : https://prove2.me/theorems/4506e390-4a1b-5444-bed1-f9b82e288162
-- title:
--   Fixed Total: sum active central cohorts eq admissible lengths
-- statement:
--   The Fixed Total construction uses the sum active central cohorts eq admissible lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L729-L741
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L729-L741

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_active_central_cohorts_eq_admissible_lengths
    (M : ℕ) (theta eta : ℝ)
    (F : Fin M → ℕ → ℝ) :
    (∑ s ∈ Finset.range (M + 1),
        ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
            (centralLevelCohortSet M s theta eta), F u s) =
      ∑ u : Fin M,
        ∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
          F u s := by sorry
