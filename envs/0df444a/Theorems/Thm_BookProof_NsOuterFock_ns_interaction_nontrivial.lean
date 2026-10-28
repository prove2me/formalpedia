-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_ns_interaction_nontrivial
-- name    : BookProof.NsOuterFock.ns_interaction_nontrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:28:16.20798+00:00
-- url     : https://prove2.me/theorems/6422734c-7a7a-4093-a168-a4af200d2910
-- title:
--   `BookProof.NsOuterFock.ns_interaction_nontrivial` {n : ℕ} (hn : 2 ≤ n) (hlam : lam ≠ 0) : ∃ (r : Fin n × NsLoc) (I : Fin (n * 18)), parcelOf I ≠ r.1 ∧ nsVec bv nu lam mu gg n r I ≠
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.ns_interaction_nontrivial` {n : ℕ} (hn : 2 ≤ n) (hlam : lam ≠ 0) : ∃ (r : Fin n × NsLoc) (I : Fin (n * 18)), parcelOf I ≠ r.1 ∧ nsVec bv nu lam mu gg n r I ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.ns_interaction_nontrivial`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.ns_interaction_nontrivial
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

theorem BookProof.NsOuterFock.ns_interaction_nontrivial {n : ℕ} (hn : 2 ≤ n) (hlam : lam ≠ 0) :
    ∃ (r : Fin n × NsLoc) (I : Fin (n * 18)),
      parcelOf I ≠ r.1 ∧ nsVec bv nu lam mu gg n r I ≠ 0 := by sorry
