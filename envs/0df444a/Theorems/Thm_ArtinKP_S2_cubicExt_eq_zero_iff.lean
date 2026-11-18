-- Prove2me | Theorems.Thm_ArtinKP_S2_cubicExt_eq_zero_iff
-- name    : ArtinKP.S2.cubicExt_eq_zero_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:51.449208+00:00
-- url     : https://prove2.me/theorems/67053440-54cb-4944-958c-01bda37d7fd6
-- title:
--   ArtinKP.S2.cubicExt_eq_zero_iff: the exterior cubic residue symbol (d/c) vanishes exactly when d and c are not coprime
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume that a cubic symbol package $P$ exists, that `ArtinKP.A.Good` $\mathfrak m$ holds, and that $\mathcal O_F$ contains a primitive sixth root of unity $z_6$ (these are hypotheses of the statement although the symbol does not depend on them). Then for all $d,c\in R$ with $c\neq 0$:
--   $$(d/c)=0\iff d\text{ and }c\text{ are not coprime in }R,$$
--   coprime meaning $xd+yc=1$ for some $x,y\in R$.
--
--   **Role in the argument.** It is the zero pattern that lets $(d/c)$ serve as the cubic symbol of the Gauss sums and of the Kubota Dirichlet series: the definition `ArtinKP.S2.cubicSymbol`, which packages $(d/c)$ with its multiplicativity laws, uses it.
--
--   **The statement**, as published (namespace `ArtinKP.S2`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A`):
--
--   ```lean
--   theorem cubicExt_eq_zero_iff (d c : SInt 𝔪) (hc : c ≠ 0) :
--       cubicExt ι 𝔪 d c = 0 ↔ ¬ IsCoprime d c
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.cubicExt` (definitions bundle `ArtinKPB000` of this split).
--
--   **Used by.** The proofs of `ArtinKP.B.eis_eq_add_tsum_Tfun` and `ArtinKP.B.tsum_lintegral_hI_ne_top` and the definitions bundle `ArtinKPB002` of this split import it.
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
import Definitions.Def_ArtinKPB000

section

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section symbol

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include P hG hz6 in
theorem cubicExt_eq_zero_iff (d c : SInt 𝔪) (hc : c ≠ 0) :
    cubicExt ι 𝔪 d c = 0 ↔ ¬ IsCoprime d c := by
  sorry

end symbol

end ArtinKP.S2
end
end
