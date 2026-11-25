-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_divIneqRecordFine6
-- name    : Formalism.DimensionVariation.divIneqRecordFine6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:56.546866+00:00
-- url     : https://prove2.me/theorems/9d393c1b-ac43-4fb5-9c37-0d03cf62153f
-- title:
--   Dimension Variation: div Ineq Record Fine6
-- statement:
--   The Dimension Variation construction uses the div Ineq Record Fine6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L105-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L105-L140

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)

theorem Formalism.DimensionVariation.divIneqRecordFine6
    (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 Nc c m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (q1 : muC ≤ mu0 + Lpass)
    (q2 : mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (q6 : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (q7 : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ)
    (z1 : 1 ≤ x) (z2 : 0 < eps) (z3 : L = x ^ eps) (z4 : b = Real.exp L) (z5 : a = x * b)
    (z6 : 1 ≤ rd) (z7 : Real.log rd ≤ L) (z8 : Real.log x ≤ L) (z9 : La = Real.log (a * rd))
    (z10 : B0 = f * m * b * x ^ eps)
    (z13 : (Fintype.card J : ℝ) = m) (z14 : (Fintype.card Pl : ℝ) ≤ f) (z15 : 1 ≤ m) (z16 : 1 ≤ f)
    (z17 : 1 ≤ k) (z18 : 1 ≤ N) (z19 : 0 ≤ S) (z20 : 0 ≤ tt) (z21 : 0 ≤ η) (zb : 0 ≤ b')
    (z23 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b)
    (z24 : ∀ j, |pq j - k| ≤ m) (z25 : |logOm| ≤ La)
    (z26 : lam0 ≤ b) (z27 : N ^ 2 ≤ b) (z28 : m ^ 3 * N ^ 2 * L ≤ b) (z29 : m * η * N * L ≤ b)
    (z30 : k * N ≤ b) (z31 : k * S ≤ w'') (z32 : m * (tt + 1) * η ≤ w'') (z33 : N * w'' ≤ b)
    (z34 : b' * N ≤ a) (z35 : m * k * b' ≤ a)
    (hC : 0 ≤ C) (hCC : C ≤ C0) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : 0 ≤ L') (hCL : C * L' ≤ C0 * La)
    (y1 : Lpass ≤ 1 + C0 * lam0)
    (y5 : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La)
    (y6 : ∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0)))
    (z11 : 0 ≤ Nc) (y2 : Eb ≤ c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc))) :
    muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
      (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by sorry
