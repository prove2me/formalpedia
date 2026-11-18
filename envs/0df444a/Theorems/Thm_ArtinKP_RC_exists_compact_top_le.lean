-- Prove2me | Theorems.Thm_ArtinKP_RC_exists_compact_top_le
-- name    : ArtinKP.RC.exists_compact_top_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:59.616944+00:00
-- url     : https://prove2.me/theorems/c37cc806-2e4d-40c7-92ab-e0b4a10017d0
-- title:
--   ArtinKP.RC.exists_compact_top_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.RC`, with `open scoped MatrixGroups ComplexConjugate ENNReal Pointwise`, `open MeasureTheory Set NumberField Module`, `open ArtinKP.X ArtinKP.B1`):
--
--   ```lean
--   theorem exists_compact_top_le (hB : SBezout S) (hO : FiniteCusps S) (T : ℝ) :
--       ∃ K : Set (X F), IsCompact K ∧ ∀ P : X F, (∀ p : PairClass S, p.ht P ≤ T) →
--         ∃ γ : SL(2, 𝓞 F), γ • P ∈ K
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B1.FiniteCusps`, `ArtinKP.B1.PairClass`, `ArtinKP.B1.SBezout` and `ArtinKP.B1.PairClass.ht` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.RC.exists_isWeakSol_of_lap_eq` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox

open scoped MatrixGroups ComplexConjugate ENNReal Pointwise
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

theorem exists_compact_top_le (hB : SBezout S) (hO : FiniteCusps S) (T : ℝ) :
    ∃ K : Set (X F), IsCompact K ∧ ∀ P : X F, (∀ p : PairClass S, p.ht P ≤ T) →
      ∃ γ : SL(2, 𝓞 F), γ • P ∈ K := by
  sorry

end

end ArtinKP.RC
end
