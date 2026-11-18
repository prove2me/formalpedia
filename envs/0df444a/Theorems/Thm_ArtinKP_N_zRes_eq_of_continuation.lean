-- Prove2me | Theorems.Thm_ArtinKP_N_zRes_eq_of_continuation
-- name    : ArtinKP.N.zRes_eq_of_continuation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:59.700441+00:00
-- url     : https://prove2.me/theorems/e82231e6-9a2e-4533-916f-6bb260bdfae1
-- title:
--   ArtinKP.N.zRes_eq_of_continuation: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF`):
--
--   ```lean
--   theorem zRes_eq_of_continuation (hD : Cell Γ D n) (hn : 1 ≤ n) {m' : ℂ → ℂ}
--       (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
--       (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
--       zRes Γ Ψ D n = z
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.C5.EisEigen`, `ArtinKP.C5.Inv`, `ArtinKP.E.slit` and `ArtinKP.N.ray` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.Cell`, `ArtinKP.N.mD` and `ArtinKP.N.zRes` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.F.zPsi_translate_nMat` of this split imports it.
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
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

section

variable (hG : Good 𝔪) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) {D : Set (InfinitePlace F → ℂ)} {n n' : ℕ}
  {φ φ' : (InfinitePlace F → ℝ) → ℂ}

include hG hΓ hE in
theorem zRes_eq_of_continuation (hD : Cell Γ D n) (hn : 1 ≤ n) {m' : ℂ → ℂ}
    (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    zRes Γ Ψ D n = z := by
  sorry

end

end

end ArtinKP.N
end
