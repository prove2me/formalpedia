-- Prove2me | Theorems.Thm_ArtinKP_H_summable_reflected_coef
-- name    : ArtinKP.H.summable_reflected_coef
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:00.356227+00:00
-- url     : https://prove2.me/theorems/d50742b0-3b8b-4e3b-bd0c-33f65224e3f7
-- title:
--   ArtinKP.H.summable_reflected_coef: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.H`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`):
--
--   ```lean
--   theorem summable_reflected_coef (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
--       (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y)
--       (hbf : ∀ σ : ℝ, 0 ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
--       (coef : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) {C : ℝ} (hcoef : ∀ ν, ‖coef ν‖ ≤ C)
--       (cl : {ν : SInt 𝔪 // ν ≠ 0} → SFinCls 𝔪 k) (y : SModel 𝔪 k) :
--       Summable (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
--         coef ν * H0.FmOf κ m J (cl ν) (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H0.FmOf` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.HB.kpCutNu_of_autCut2` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section general

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {κ : ℝ → ℝ} (hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ}
  (hα : 0 ≤ α)
  (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
  (m : InfinitePlace F → ℤ)

include h𝔪 g hκ0 hα hκb

theorem summable_reflected_coef (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
    (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y)
    (hbf : ∀ σ : ℝ, 0 ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (coef : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) {C : ℝ} (hcoef : ∀ ν, ‖coef ν‖ ≤ C)
    (cl : {ν : SInt 𝔪 // ν ≠ 0} → SFinCls 𝔪 k) (y : SModel 𝔪 k) :
    Summable (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      coef ν * H0.FmOf κ m J (cl ν) (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y)) := by
  sorry

end general

end

end ArtinKP.H
end
