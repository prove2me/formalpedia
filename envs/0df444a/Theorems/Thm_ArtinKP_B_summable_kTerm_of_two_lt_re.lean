-- Prove2me | Theorems.Thm_ArtinKP_B_summable_kTerm_of_two_lt_re
-- name    : ArtinKP.B.summable_kTerm_of_two_lt_re
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:28:36.667211+00:00
-- url     : https://prove2.me/theorems/dd96b213-9b48-4b36-830b-51beaaf80954
-- title:
--   ArtinKP.B.summable_kTerm_of_two_lt_re: the Kubota Dirichlet series of a genuine section converges absolutely for Re s > 2
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume $F$ is totally complex, `ArtinKP.A.Good` $\mathfrak m$, and that $\mathcal O_F$ contains a primitive sixth root of unity $z_6$. Let $P$ be a cubic symbol package, $\Phi$ a genuine section (`ArtinKP.S.GSection` $\iota\,P\,\mathfrak m$: a family $s\mapsto\Phi_s$ of functions on $F\times F$, holomorphic in $s$, vanishing at $(0,0)$, with the prescribed transformation under $S$-units and under cubes, a level condition expressed through Kubota's $\sigma_S$, and a polynomial bound), and $\nu\in R$ any element ($\nu=0$ included). Then for every complex $s$ with $\operatorname{Re}s>2$ the family
--   $$a\longmapsto \texttt{kTerm}(a,s)=g(\nu;c)\cdot\Lambda_\Phi(c,\nu,s)\cdot N(c)^{-s},\qquad c\text{ the chosen representative of }a,$$
--   indexed by the nonzero classes $a$ of $R$ modulo units (`ArtinKP.E.Cls`), is summable. Here (`ArtinKP.B.kTerm`) $g(\nu;c)$ is the Gauss sum `ArtinKP.B7.gauss` of the cubic symbol `ArtinKP.S2.cubicSymbol` $(\cdot/c)$ against the additive character `ArtinPrimitiveRoots.sAddChar` at frequency $\nu$, $\Lambda_\Phi$ is the normalized finite Jacquet factor `ArtinKP.S2.LamR` of $\Phi$ for the $S_f$-character `ArtinKP.B.psiS`, and $N(c)=\#(R/cR)$ (`ArtinKP.E.nrm`).
--
--   **Role in the argument.** It is the convergence on which the Kubota Dirichlet series $\mathfrak a_\Phi(\nu,s)=\sum_a\texttt{kTerm}(a,s)$ rests: the definition `ArtinKP.B.kubota`, which packages the series for the analysis of its residue at $s=4/3$, uses this statement.
--
--   **The statement**, as published (namespace `ArtinKP.B`, with `open scoped MatrixGroups ComplexConjugate`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7`):
--
--   ```lean
--   theorem summable_kTerm_of_two_lt_re {s : ℂ} (hs : 2 < s.re) :
--       Summable fun a : Cls (SInt 𝔪) => kTerm hG hz6 Φ ν a s
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.kTerm`, `ArtinKP.E.Cls` and `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB015` of this split imports it.
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
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB002

section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

theorem summable_kTerm_of_two_lt_re {s : ℂ} (hs : 2 < s.re) :
    Summable fun a : Cls (SInt 𝔪) => kTerm hG hz6 Φ ν a s := by
  sorry

end ArtinKP.B
end
end
