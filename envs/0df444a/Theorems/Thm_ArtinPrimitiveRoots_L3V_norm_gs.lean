-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_L3V_norm_gs
-- name    : ArtinPrimitiveRoots.L3V.norm_gs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:12:31.227337+00:00
-- url     : https://prove2.me/theorems/bf650b47-90cb-48bb-834a-01b3892b264a
-- title:
--   ArtinPrimitiveRoots.L3V.norm_gs: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinPrimitiveRoots.L3V`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero`):
--
--   ```lean
--   lemma norm_gs {m : ℕ} (hm : ¬ 6 ∣ m) :
--       ‖gaussSum (C3I.chi ι h hω ^ m) (C3I.psi g h)‖ = Real.sqrt (Ideal.absNorm v.asIdeal)
--   ```
--
--   **Definitions.** The statement is written with `ArtinPrimitiveRoots.C3I.Good` and `ArtinPrimitiveRoots.C3I.chi` (definitions bundle `ArtinKPB003` of this split); `ArtinPrimitiveRoots.C3I.psi` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.H.sum_maskProd_sAddChar` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section loc

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
include h hω

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

lemma norm_gs {m : ℕ} (hm : ¬ 6 ∣ m) :
    ‖gaussSum (C3I.chi ι h hω ^ m) (C3I.psi g h)‖ = Real.sqrt (Ideal.absNorm v.asIdeal) := by
  sorry

end loc

end L3V

end ArtinPrimitiveRoots
end
