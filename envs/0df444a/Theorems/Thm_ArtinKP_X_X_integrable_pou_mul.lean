-- Prove2me | Theorems.Thm_ArtinKP_X_X_integrable_pou_mul
-- name    : ArtinKP.X.X.integrable_pou_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:10.535628+00:00
-- url     : https://prove2.me/theorems/7f1c3bfa-3779-4a46-8a5d-3c186081367d
-- title:
--   ArtinKP.X.X.integrable_pou_mul: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.integrable_pou_mul {h : X F → ℂ} (hc : Continuous h) (hinv : X.IsInv Γ h)
--       {K : Set (X F)} (hK : IsCompact K) (hsupp : ∀ P, h P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
--       Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * h P) (X.vol F)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split); `ArtinKP.X.X.IsInv` (definitions bundle `ArtinKPB010` of this split).
--
--   **Used by.** The proof of `ArtinKP.X.X.ims` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB010

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

theorem X.integrable_pou_mul {h : X F → ℂ} (hc : Continuous h) (hinv : X.IsInv Γ h)
    {K : Set (X F)} (hK : IsCompact K) (hsupp : ∀ P, h P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
    Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * h P) (X.vol F) := by
  sorry

end

end ArtinKP.X
end
