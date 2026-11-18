-- Prove2me | Theorems.Thm_ArtinKP_GR_ThetaM_flip
-- name    : ArtinKP.GR.ThetaM_flip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:11.248857+00:00
-- url     : https://prove2.me/theorems/7f5c47c3-5f9d-4ef8-bc50-56f3a8d38779
-- title:
--   ArtinKP.GR.ThetaM_flip: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GR`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K`):
--
--   ```lean
--   theorem ThetaM_flip (hE : ThmE hG hz6 g P)
--       (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
--         ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
--       (hW : WeylFlip (ι := ι) P hG hz6) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
--       (Φ : GSection ι P 𝔪) (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
--       (y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
--       ThetaM hG hz6 m Φ (emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
--           (fun w => y w ^ 2) (fun w => pow_ne_zero 2 (hy w)) =
--         (-1) ^ Fintype.card (InfinitePlace F) *
--           ThetaM hG hz6 (fun w => -m w) (S2.GSection.translate hG γ Φ)
--             (emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
--             (fun w => ((w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹) ^ 2)
--             (fun w => pow_ne_zero 2
--               (inv_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (hy w))))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B1.emb` and `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.S2.GSection.translate` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.G2a.ThetaM`, `ArtinKP.G2a.ThmE` and `ArtinKP.GR.WeylFlip` (definitions bundle `ArtinKPB017` of this split).
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

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable [IsTotallyComplex F] {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6 P)

variable {hG hz6 P}

theorem ThetaM_flip (hE : ThmE hG hz6 g P)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (hW : WeylFlip (ι := ι) P hG hz6) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
    (Φ : GSection ι P 𝔪) (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
    (y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
    ThetaM hG hz6 m Φ (emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
        (fun w => y w ^ 2) (fun w => pow_ne_zero 2 (hy w)) =
      (-1) ^ Fintype.card (InfinitePlace F) *
        ThetaM hG hz6 (fun w => -m w) (S2.GSection.translate hG γ Φ)
          (emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
          (fun w => ((w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹) ^ 2)
          (fun w => pow_ne_zero 2
            (inv_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (hy w)))) := by
  sorry

end

end ArtinKP.GR
end
