-- Prove2me | Theorems.Thm_ArtinKP_HB_finsum_maskProd_mul_digCoefNu_eq_eprod
-- name    : ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:27.192194+00:00
-- url     : https://prove2.me/theorems/ee6850bb-40b5-43b9-949a-557b212f9d9d
-- title:
--   ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.HB`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`):
--
--   ```lean
--   theorem finsum_maskProd_mul_digCoefNu_eq_eprod (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
--       (h𝔟 : IsExterior 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
--       ∑ᶠ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * digCoefNu h𝔪 g 𝔟 v ν =
--         L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (H0.rowOf h𝔪 g ν)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H.Dig`, `ArtinKP.H.maskProd`, `ArtinKP.H0.rowOf`, `ArtinKP.HB.digCoefNu`, `ArtinPrimitiveRoots.C3I.cutN` and `ArtinPrimitiveRoots.L3V.Eprod` (definitions bundle `ArtinKPB017` of this split).
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

namespace ArtinKP.HB

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

theorem finsum_maskProd_mul_digCoefNu_eq_eprod (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ∑ᶠ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * digCoefNu h𝔪 g 𝔟 v ν =
      L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (H0.rowOf h𝔪 g ν) := by
  sorry

end good

end

end ArtinKP.HB
end
