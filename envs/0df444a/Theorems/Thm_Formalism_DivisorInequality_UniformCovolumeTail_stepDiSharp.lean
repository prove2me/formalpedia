-- Prove2me | Theorems.Thm_Formalism_DivisorInequality_UniformCovolumeTail_stepDiSharp
-- name    : Formalism.DivisorInequality.UniformCovolumeTail.stepDiSharp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:17.665793+00:00
-- url     : https://prove2.me/theorems/186a2099-d209-41d9-bd3f-18183fa0e2ce
-- title:
--   Uniform Covolume Tail: step Di Sharp
-- statement:
--   The Uniform Covolume Tail construction uses the step Di Sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DivisorInequality/DivisorInequalityProofs/EvenDegreeWeightBounds.lean#L27-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DivisorInequality/DivisorInequalityProofs/EvenDegreeWeightBounds.lean#L27-L148

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_DivIneqTopAnchorU
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisorInequality.UniformCovolumeTail
set_option maxHeartbeats 800000

theorem Formalism.DivisorInequality.UniformCovolumeTail.stepDiSharp (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 Ce Ch : ℝ)
    (h32 : ∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j)))
    (hmean : ∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ))
    (hOm : ∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm)
    (hSK : ∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg)
    (hth : (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L)
    (hh : ∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hh' : ∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hcard : (Fintype.card Pl : ℝ) ≤ f) (hg0 : ∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hL : 0 ≤ L) (hLLa : L ≤ La) (hLa1 : 1 ≤ La)
    (h5 : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La)
    (h6 : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La)
    (hT : logT ≤ C7 * m * L) (hg : logg ≤ C8 * L)
    (p2 : 0 ≤ C2) (p3 : 0 ≤ C3) (p4 : 0 ≤ C4) (p5 : 0 ≤ c5) (p6 : 0 ≤ c6) (p7 : 0 ≤ C7) (p8 : 0 ≤ C8)
    (pe : 0 ≤ Ce)
    (kA : C3 + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ Ch) (kB : 2 * (C2 + C4) * (C7 + C8) ≤ Ch) :
    ∀ j, hK j ≤ ∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) +
      Ch * f * N ^ 2 * (La + m ^ 3 * L) := by sorry
