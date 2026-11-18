-- Prove2me | Theorems.Thm_ArtinKP_G2a_integral_strip_term
-- name    : ArtinKP.G2a.integral_strip_term
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:28.880921+00:00
-- url     : https://prove2.me/theorems/11f251ad-97c9-43de-8b4d-4ce95a4c2c15
-- title:
--   ArtinKP.G2a.integral_strip_term: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G2a`, with `open scoped ComplexConjugate Topology MatrixGroups`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N`):
--
--   ```lean
--   theorem integral_strip_term (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
--       ∫ Q in X.box n, conj (stripFn D ν' φ Q) * term hG hz6 Φ ν Q ∂X.vol F =
--         if T.freq ((ν : SInt 𝔪) : F) = ν' then
--           T.tau hG hz6 Φ (ν : SInt 𝔪) * T.Wc D n φ ((ν : SInt 𝔪) : F) (4 / 3) else 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.X.box` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.C5.Inv`, `ArtinKP.RF.stripFn`, `ArtinKP.T.Wc`, `ArtinKP.T.freq`, `ArtinKP.T.tau`, `ArtinKP.X.GammaN` and `ArtinKP.X.GammaN.shift` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.G2a.term` and `ArtinKP.RF.dualLat` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.G2a.coeff_thetaS_freq` and `ArtinKP.G2a.coeff_thetaS_of_ne` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex

open scoped ComplexConjugate Topology MatrixGroups
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

section strip

variable (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
  (hΓ : Inv Γ (Φ.twist hG hz6)) {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
  (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
  {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {ν' : InfinitePlace F → ℂ} (hν' : ν' ∈ dualLat Γ)
  {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)

include hΓ hD hfund hb hν' hφ hφ1 in
theorem integral_strip_term (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ∫ Q in X.box n, conj (stripFn D ν' φ Q) * term hG hz6 Φ ν Q ∂X.vol F =
      if T.freq ((ν : SInt 𝔪) : F) = ν' then
        T.tau hG hz6 Φ (ν : SInt 𝔪) * T.Wc D n φ ((ν : SInt 𝔪) : F) (4 / 3) else 0 := by
  sorry

end strip

end

end ArtinKP.G2a
end
