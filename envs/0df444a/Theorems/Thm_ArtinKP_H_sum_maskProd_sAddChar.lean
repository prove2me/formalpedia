-- Prove2me | Theorems.Thm_ArtinKP_H_sum_maskProd_sAddChar
-- name    : ArtinKP.H.sum_maskProd_sAddChar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:46.756202+00:00
-- url     : https://prove2.me/theorems/b0604c1b-cb9a-4157-a8e5-a479d7b8380b
-- title:
--   ArtinKP.H.sum_maskProd_sAddChar: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.H`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`):
--
--   ```lean
--   theorem sum_maskProd_sAddChar (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
--       (x : SInt 𝔪) :
--       ∑ᶠ v : Dig 𝔪 𝔟, maskProd g 𝔟 v * sAddChar 𝔪 ((x : F) * xdig g 𝔟 v) =
--         residueSymbol ι 𝔪 𝔟 x
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H.Dig`, `ArtinKP.H.maskProd`, `ArtinKP.H.xdig` and `ArtinPrimitiveRoots.C3I.cutN` (definitions bundle `ArtinKPB017` of this split).
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
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section good

variable (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] {N₀ : ℕ}
  (hN₀ : C3I.cutN F ≤ N₀) (hsm : SmallPrimesDvd N₀ 𝔪)

include hn0 hn hN₀ hsm

theorem sum_maskProd_sAddChar (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (x : SInt 𝔪) :
    ∑ᶠ v : Dig 𝔪 𝔟, maskProd g 𝔟 v * sAddChar 𝔪 ((x : F) * xdig g 𝔟 v) =
      residueSymbol ι 𝔪 𝔟 x := by
  sorry

end good

end

end ArtinKP.H
end
