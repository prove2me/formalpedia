-- Prove2me | Theorems.Thm_ArtinKP_X_X_ims
-- name    : ArtinKP.X.X.ims
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:44.994449+00:00
-- url     : https://prove2.me/theorems/32d5be47-d024-43c7-a524-d1e7ad971596
-- title:
--   ArtinKP.X.X.ims: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.ims {c : X F → ℝ} (hcs : X.Smooth fun P => (c P : ℂ)) (hcinv : X.IsInv Γ c)
--       {K : Set (X F)} (hK : IsCompact K) (hcK : ∀ P, c P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
--       {u : X F → ℂ} (hu : X.Smooth u) (hinv : X.IsInv Γ u)
--       (a : X.core Γ) (ha : (a : X F → ℂ) = fun P => (c P : ℂ) * u P) :
--       Integrable (fun P => (X.pou Γ P).toReal *
--           (c P ^ 2 * (conj (u P) * X.lap u P).re +
--             ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P)) (X.vol F) ∧
--         ∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F =
--           ∫ P, (X.pou Γ P).toReal *
--             (c P ^ 2 * (conj (u P) * X.lap u P).re +
--               ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P) ∂X.vol F
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.Smooth`, `ArtinKP.X.X.core`, `ArtinKP.X.X.lap` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split); `ArtinKP.X.X.IsInv` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.grad2` (definitions bundle `ArtinKPB014` of this split).
--
--   **Used by.** The proof of `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB010
import Definitions.Def_ArtinKPB014

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

theorem X.ims {c : X F → ℝ} (hcs : X.Smooth fun P => (c P : ℂ)) (hcinv : X.IsInv Γ c)
    {K : Set (X F)} (hK : IsCompact K) (hcK : ∀ P, c P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
    {u : X F → ℂ} (hu : X.Smooth u) (hinv : X.IsInv Γ u)
    (a : X.core Γ) (ha : (a : X F → ℂ) = fun P => (c P : ℂ) * u P) :
    Integrable (fun P => (X.pou Γ P).toReal *
        (c P ^ 2 * (conj (u P) * X.lap u P).re +
          ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P)) (X.vol F) ∧
      ∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F =
        ∫ P, (X.pou Γ P).toReal *
          (c P ^ 2 * (conj (u P) * X.lap u P).re +
            ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P) ∂X.vol F := by
  sorry

end

end ArtinKP.X
end
