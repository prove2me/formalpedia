-- Prove2me | Theorems.Thm_ArtinKP_H0_FmOf_clauses
-- name    : ArtinKP.H0.FmOf_clauses
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:22.500725+00:00
-- url     : https://prove2.me/theorems/fe93fd01-c6cb-4582-966a-b4ec44c9a869
-- title:
--   ArtinKP.H0.FmOf_clauses: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.H0`, with `open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`):
--
--   ```lean
--   theorem FmOf_clauses {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (hα' : α ≤ 5 / 6)
--       (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
--       (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y) :
--       (∀ cl, Measurable (FmOf (K.kappaB c) m J cl)) ∧ (∀ y, 0 ≤ bf y) ∧
--       (∀ w cl y, ContDiff ℝ 2
--         (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
--       (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w cl y, ∀ j : ℕ, j ≤ 2 →
--         ‖iteratedDeriv j
--             (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
--           C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H0.FmOf` and `ArtinKP.K.kappaB` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.H0.goal_of_KPCut` of this split imports it.
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

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ)

theorem FmOf_clauses {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (hα' : α ≤ 5 / 6)
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
    (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y) :
    (∀ cl, Measurable (FmOf (K.kappaB c) m J cl)) ∧ (∀ y, 0 ≤ bf y) ∧
    (∀ w cl y, ContDiff ℝ 2
      (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
    (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w cl y, ∀ j : ℕ, j ≤ 2 →
      ‖iteratedDeriv j
          (fun s : ℝ => FmOf (K.kappaB c) m J cl (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
        C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) := by
  sorry

end

end ArtinKP.H0
end
