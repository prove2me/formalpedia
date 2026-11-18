-- Prove2me | Theorems.Thm_ArtinKP_GR_thetaG_eq_tsum_forward
-- name    : ArtinKP.GR.thetaG_eq_tsum_forward
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:32.26166+00:00
-- url     : https://prove2.me/theorems/802f3075-f6c3-4e6a-b574-e8a0d8fff416
-- title:
--   ArtinKP.GR.thetaG_eq_tsum_forward: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.GR`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K`):
--
--   ```lean
--   theorem thetaG_eq_tsum_forward (hE : ThmE hG hz6 g P) (hk : P.IsDeepLevel 𝔪 (k + 1))
--       {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
--       (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F) (y : SModel 𝔪 k) :
--       ThetaG hG hz6 m Φ₀ x y =
--         ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * x)) *
--           (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
--             L3X.fpF (kappaB (4 * Real.pi)) m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.G2a.ThmE`, `ArtinKP.GK.IsDelta`, `ArtinKP.GR.ThetaG`, `ArtinKP.H0.rowOf`, `ArtinKP.K.kappaB`, `ArtinPrimitiveRoots.L3X.coefF'` and `ArtinPrimitiveRoots.L3X.fpF` (definitions bundle `ArtinKPB017` of this split).
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

theorem thetaG_eq_tsum_forward (hE : ThmE hG hz6 g P) (hk : P.IsDeepLevel 𝔪 (k + 1))
    {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
    (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F) (y : SModel 𝔪 k) :
    ThetaG hG hz6 m Φ₀ x y =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * x)) *
        (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
          L3X.fpF (kappaB (4 * Real.pi)) m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y)) := by
  sorry

end

end ArtinKP.GR
end
