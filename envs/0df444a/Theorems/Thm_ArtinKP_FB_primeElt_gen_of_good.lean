-- Prove2me | Theorems.Thm_ArtinKP_FB_primeElt_gen_of_good
-- name    : ArtinKP.FB.primeElt_gen_of_good
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:30:07.004331+00:00
-- url     : https://prove2.me/theorems/a30321e0-b1da-4060-a0f5-c7b28cd65923
-- title:
--   ArtinKP.FB.primeElt_gen_of_good: the allowed generator of a good exterior prime is a prime element with a nontrivial cubic symbol
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume a cubic symbol package $P$, `ArtinKP.A.Good` $\mathfrak m$, a primitive sixth root of unity $z_6\in\mathcal O_F$, and a system of allowed generators $g$ (`ArtinPrimitiveRoots.AllowedGen` $\iota\,\mathfrak m$: for each exterior ideal $I$ an element $g(I)\in R$ generating $IR$, multiplicative up to sixth powers of $S$-units, with sextic reciprocity between the generators of distinct exterior primes). Let $v$ be a prime of $\mathcal O_F$ that is good in the sense of `ArtinPrimitiveRoots.C3I.Good` $\mathfrak m\,v$: $v+\mathfrak m=\mathcal O_F$, $12$ divides $N(v)-1$, and $v$ does not contain the different ideal of $F/\mathbb Q$. Then $\pi=g(v)$ satisfies `ArtinKP.FA.PrimeElt` $\iota\,\mathfrak m\,v\,\pi$:
--
--   - $\pi\neq 0$;
--   - the principal ideal $\pi R$ is a maximal ideal of $R$;
--   - $v(\pi)<1$, that is, $\pi$ has positive $v$-adic order;
--   - there is $u\in R$ with $\pi\nmid u$ in $R$ and $(u/\pi)\neq 1$, where $(u/\pi)$ is the exterior cubic residue symbol.
--
--   **Role in the argument.** At a good exterior prime the generator $\pi$ is the uniformizer used in the cube-periodicity of the theta coefficients, $\tau(\nu\pi^3)$ against $\tau(\nu)$; the proofs of `ArtinKP.F.mD_restrict` and `ArtinKP.GK.theta_per_gen_of_isExterior` use this statement.
--
--   **The statement**, as published (namespace `ArtinKP.FB`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B`):
--
--   ```lean
--   theorem primeElt_gen_of_good (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
--       (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) : PrimeElt ι 𝔪 v (g.gen v.asIdeal)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.FA.PrimeElt` and `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split).
--
--   **Used by.** The proofs of `ArtinKP.F.mD_restrict` and `ArtinKP.GK.theta_per_gen_of_isExterior` of this split import it.
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
import Definitions.Def_ArtinKPB003

section

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

theorem primeElt_gen_of_good (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) : PrimeElt ι 𝔪 v (g.gen v.asIdeal) := by
  sorry

end ArtinKP.FB
end
end
