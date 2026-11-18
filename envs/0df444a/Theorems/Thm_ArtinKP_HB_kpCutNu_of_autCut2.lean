-- Prove2me | Theorems.Thm_ArtinKP_HB_kpCutNu_of_autCut2
-- name    : ArtinKP.HB.kpCutNu_of_autCut2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:52.859521+00:00
-- url     : https://prove2.me/theorems/d2e15d30-526e-49d6-a465-8caf355ae017
-- title:
--   ArtinKP.HB.kpCutNu_of_autCut2: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.HB`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`):
--
--   ```lean
--   theorem kpCutNu_of_autCut2 (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
--       (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
--       (h : AutCut2 n F ι) :
--       H0.KPCutNu n F ι
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H0.KPCutNu` and `ArtinKP.HB.AutCut2` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant` of this split imports it.
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

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem kpCutNu_of_autCut2 (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : AutCut2 n F ι) :
    H0.KPCutNu n F ι := by
  sorry

end

end ArtinKP.HB
end
