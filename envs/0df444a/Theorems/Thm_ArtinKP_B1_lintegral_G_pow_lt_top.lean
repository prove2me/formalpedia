-- Prove2me | Theorems.Thm_ArtinKP_B1_lintegral_G_pow_lt_top
-- name    : ArtinKP.B1.lintegral_G_pow_lt_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:49.456032+00:00
-- url     : https://prove2.me/theorems/6c6104b1-c2a6-4da0-b707-936380801171
-- title:
--   ArtinKP.B1.lintegral_G_pow_lt_top: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.B1`, with `open scoped MatrixGroups ComplexConjugate ENNReal`, `open MeasureTheory Set NumberField Module`, `open ArtinKP.X`):
--
--   ```lean
--   theorem lintegral_G_pow_lt_top (hB : SBezout S) (hO : FiniteCusps S) {σ : ℝ} (hσ : 2 < σ)
--       (Γ : Subgroup (SL(2, 𝓞 F))) (hvol : X.quotVol Γ Set.univ < ⊤) (k : ℕ) :
--       ∫⁻ P, ENNReal.ofReal (G S σ P) ^ k * X.pou Γ P ∂X.vol F < ⊤
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.B1.FiniteCusps`, `ArtinKP.B1.G` and `ArtinKP.B1.SBezout` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.RC.lintegral_G_pow_lt_top` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

theorem lintegral_G_pow_lt_top (hB : SBezout S) (hO : FiniteCusps S) {σ : ℝ} (hσ : 2 < σ)
    (Γ : Subgroup (SL(2, 𝓞 F))) (hvol : X.quotVol Γ Set.univ < ⊤) (k : ℕ) :
    ∫⁻ P, ENNReal.ofReal (G S σ P) ^ k * X.pou Γ P ∂X.vol F < ⊤ := by
  sorry

end

end ArtinKP.B1
end
