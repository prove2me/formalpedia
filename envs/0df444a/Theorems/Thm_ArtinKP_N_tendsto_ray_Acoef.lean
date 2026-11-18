-- Prove2me | Theorems.Thm_ArtinKP_N_tendsto_ray_Acoef
-- name    : ArtinKP.N.tendsto_ray_Acoef
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:44.417522+00:00
-- url     : https://prove2.me/theorems/df6e850a-7133-4e57-8e55-2bdaeb35e9c1
-- title:
--   ArtinKP.N.tendsto_ray_Acoef: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF`):
--
--   ```lean
--   theorem tendsto_ray_Acoef (hDm : MeasurableSet D) (n : ℕ) (hφ : Measurable φ)
--       (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
--       Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * Acoef Γ Ψ D n φ (ray t)) (𝓝[>] 0)
--         (𝓝 (cf D n φ (X.lift Γ (theta Γ Ψ))))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X.lift` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv`, `ArtinKP.C5.theta`, `ArtinKP.N.cf` and `ArtinKP.N.ray` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.Acoef` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.F.tendsto_mext_zPsi`, `ArtinKP.F.zPsi_add` and `ArtinKP.F.zPsi_smul` of this split import it.
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

include hG hΓ in
theorem tendsto_ray_Acoef (hDm : MeasurableSet D) (n : ℕ) (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * Acoef Γ Ψ D n φ (ray t)) (𝓝[>] 0)
      (𝓝 (cf D n φ (X.lift Γ (theta Γ Ψ)))) := by
  sorry

end

end

end ArtinKP.N
end
