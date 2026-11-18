-- Prove2me | Theorems.Thm_ArtinKP_GK_xi_wSec_phiB_eq_jdef
-- name    : ArtinKP.GK.xi_wSec_phiB_eq_jdef
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:58.106618+00:00
-- url     : https://prove2.me/theorems/5477bd86-a1a4-41a1-aa0c-0eb7f3668393
-- title:
--   ArtinKP.GK.xi_wSec_phiB_eq_jdef: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GK`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B7`):
--
--   ```lean
--   theorem xi_wSec_phiB_eq_jdef (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
--       (hΦ₀ : IsDelta hG hz6 k Φ₀) (β₀ : Fˣ) (ν' : Fˣ) :
--       (-1) ^ Fintype.card (InfinitePlace F)
--           * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG (PhiB hG Φ₀ β₀)) (ν' : F)
--         = Jdef hG hz6 Φ₀ (QuotientAddGroup.mk (SFin.mk 𝔪 k ν'))
--             (SFin.mk 𝔪 k ν' - SFin.mk 𝔪 k β₀)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.G1.wSec`, `ArtinKP.G1.xi`, `ArtinKP.GK.Jdef` and `ArtinKP.T.theta` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.DD.DiffInS`, `ArtinKP.GK.IsDelta` and `ArtinKP.GK.PhiB` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.thetaG_eq_tsum_reflected` of this split imports it.
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

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {k : ℕ}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

section delta

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hd : DD.DiffInS 𝔪)

include g hgood hd in
theorem xi_wSec_phiB_eq_jdef (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : IsDelta hG hz6 k Φ₀) (β₀ : Fˣ) (ν' : Fˣ) :
    (-1) ^ Fintype.card (InfinitePlace F)
        * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG (PhiB hG Φ₀ β₀)) (ν' : F)
      = Jdef hG hz6 Φ₀ (QuotientAddGroup.mk (SFin.mk 𝔪 k ν'))
          (SFin.mk 𝔪 k ν' - SFin.mk 𝔪 k β₀) := by
  sorry

end delta

end

end ArtinKP.GK
end
