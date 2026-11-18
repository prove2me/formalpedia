-- Prove2me | Theorems.Thm_ArtinKP_K_kappaB_iteratedDeriv_bound_shift
-- name    : ArtinKP.K.kappaB_iteratedDeriv_bound_shift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:25.135027+00:00
-- url     : https://prove2.me/theorems/de07d698-d252-43e1-bf69-067f6a2fbdde
-- title:
--   ArtinKP.K.kappaB_iteratedDeriv_bound_shift: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.K`, with `open MeasureTheory Set Filter`, `open ArtinPrimitiveRoots.L3J (gA kappa0 )`):
--
--   ```lean
--   theorem kappaB_iteratedDeriv_bound_shift {c : ℝ} (hc : 0 < c) {α N : ℝ} (hα : 0 < α)
--       (hα' : α ≤ 5 / 6) (hN : 0 < N) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
--         |iteratedDeriv j (fun s : ℝ => kappaB c (Real.exp (x + s))) 0| ≤
--           C * min (Real.exp (α * x)) (Real.exp (-(N * x)))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.K.kappaB` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.H0.FmOf_clauses` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinKPB017

section

namespace ArtinKP.K

open MeasureTheory Set Filter
open ArtinPrimitiveRoots.L3J (gA kappa0 )

noncomputable section

theorem kappaB_iteratedDeriv_bound_shift {c : ℝ} (hc : 0 < c) {α N : ℝ} (hα : 0 < α)
    (hα' : α ≤ 5 / 6) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (fun s : ℝ => kappaB c (Real.exp (x + s))) 0| ≤
        C * min (Real.exp (α * x)) (Real.exp (-(N * x))) := by
  sorry

end

end ArtinKP.K
end
