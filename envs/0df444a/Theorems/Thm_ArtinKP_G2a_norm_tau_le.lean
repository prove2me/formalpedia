-- Prove2me | Theorems.Thm_ArtinKP_G2a_norm_tau_le
-- name    : ArtinKP.G2a.norm_tau_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:47.171876+00:00
-- url     : https://prove2.me/theorems/567889af-01c8-430b-9147-a0b38e857476
-- title:
--   ArtinKP.G2a.norm_tau_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.G2a`, with `open scoped ComplexConjugate Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF`):
--
--   ```lean
--   theorem norm_tau_le (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) :
--       ∃ bf : SFin 𝔪 0 → ℝ, (∀ y, 0 ≤ bf y) ∧
--         (∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 0 => bf y * SFin.norm y ^ σ)) ∧
--         ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ ≤
--           (∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
--             bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.T.tau` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.G2a.ThmE` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.G2a.coeff_thetaS_of_ne`, `ArtinKP.G2a.continuous_thetaS`, `ArtinKP.G2a.exists_major` and `ArtinKP.G2a.exists_major_prod` of this split import it.
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

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (g : AllowedGen ι 𝔪)

variable {hG hz6 g}

theorem norm_tau_le (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) :
    ∃ bf : SFin 𝔪 0 → ℝ, (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 0 => bf y * SFin.norm y ^ σ)) ∧
      ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ ≤
        (∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
          bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2 := by
  sorry

end

end ArtinKP.G2a
end
