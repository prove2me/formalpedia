-- Prove2me | Theorems.Thm_ArtinKP_G2a_ThetaM_nT
-- name    : ArtinKP.G2a.ThetaM_nT
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:05:22.009198+00:00
-- url     : https://prove2.me/theorems/d654f542-73b9-45e2-9bd1-a7e8a2aacb76
-- title:
--   ArtinKP.G2a.ThetaM_nT: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G2a`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K`):
--
--   ```lean
--   theorem ThetaM_nT (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
--       (t : F) (Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) :
--       ThetaM hG hz6 m (Φ.nT hG t) (emb t) Y hY =
--         kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
--           ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (((ν : SInt 𝔪) : F) * t) *
--             (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
--               G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) *
--               ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
--                 (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ)))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B1.emb`, `ArtinKP.S.GSection` and `ArtinKP.S.GSection.nT` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.G1.xi` and `ArtinKP.T.theta` (definitions bundle `ArtinKPB016` of this split); `ArtinKP.G2a.C0`, `ArtinKP.G2a.ThetaM`, `ArtinKP.G2a.ThmE`, `ArtinKP.G2a.kapC`, `ArtinKP.G2a.omg`, `ArtinKP.H0.rowOf`, `ArtinKP.K.kappaB` and `ArtinPrimitiveRoots.L3X.coefF'` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.thetaG_eq_tsum_forward` of this split imports it.
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

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

variable {hG hz6}

theorem ThetaM_nT (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (t : F) (Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) :
    ThetaM hG hz6 m (Φ.nT hG t) (emb t) Y hY =
      kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (((ν : SInt 𝔪) : F) * t) *
          (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
            G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) *
            ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
              (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ))) := by
  sorry

end

end ArtinKP.G2a
end
