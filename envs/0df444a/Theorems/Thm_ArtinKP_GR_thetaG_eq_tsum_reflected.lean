-- Prove2me | Theorems.Thm_ArtinKP_GR_thetaG_eq_tsum_reflected
-- name    : ArtinKP.GR.thetaG_eq_tsum_reflected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:37.55138+00:00
-- url     : https://prove2.me/theorems/8d6a03fc-94e3-4285-ab57-9f49fc1b6cb9
-- title:
--   ArtinKP.GR.thetaG_eq_tsum_reflected: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GR`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K`):
--
--   ```lean
--   theorem thetaG_eq_tsum_reflected (hE : ThmE hG hz6 g P)
--       (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
--         C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
--       (hd : DD.DiffInS 𝔪) (hW : WeylFlip (ι := ι) P hG hz6)
--       (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
--       (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F)
--       (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
--       (hdx : ((γ.1 1 1 : SInt 𝔪) : F) = ((γ.1 1 0 : SInt 𝔪) : F) * x) (y : SModel 𝔪 k) :
--       ThetaG hG hz6 m Φ₀ x y =
--         ∑' μ : {μ : SInt 𝔪 // μ ≠ 0},
--           (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g μ) *
--             sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) *
--             kappa ι 𝔪 γ * brk ι P 𝔪 ((μ : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F)) *
--           H0.FmOf (kappaB (4 * Real.pi)) m (GK.Jdef hG hz6 Φ₀)
--             (QuotientAddGroup.mk
--               (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2)).2.2)
--             (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2) - y)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good`, `ArtinKP.A.kappa` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.brk` (definitions bundle `ArtinKPB002` of this split); `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.GK.Jdef` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.DD.DiffInS`, `ArtinKP.G2a.ThmE`, `ArtinKP.GK.IsDelta`, `ArtinKP.GR.ThetaG`, `ArtinKP.GR.WeylFlip`, `ArtinKP.H0.FmOf`, `ArtinKP.H0.rowOf`, `ArtinKP.K.kappaB` and `ArtinPrimitiveRoots.L3X.coefF'` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.secCut_of_isCyclotomicExtension` of this split imports it.
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

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {k : ℕ}

variable {hG hz6}

variable {g : AllowedGen ι 𝔪}

theorem thetaG_eq_tsum_reflected (hE : ThmE hG hz6 g P)
    (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
      C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
    (hd : DD.DiffInS 𝔪) (hW : WeylFlip (ι := ι) P hG hz6)
    (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
    (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F)
    (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
    (hdx : ((γ.1 1 1 : SInt 𝔪) : F) = ((γ.1 1 0 : SInt 𝔪) : F) * x) (y : SModel 𝔪 k) :
    ThetaG hG hz6 m Φ₀ x y =
      ∑' μ : {μ : SInt 𝔪 // μ ≠ 0},
        (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g μ) *
          sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) *
          kappa ι 𝔪 γ * brk ι P 𝔪 ((μ : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F)) *
        H0.FmOf (kappaB (4 * Real.pi)) m (GK.Jdef hG hz6 Φ₀)
          (QuotientAddGroup.mk
            (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2)).2.2)
          (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2) - y) := by
  sorry

end

end ArtinKP.GR
end
