-- Prove2me | Theorems.Thm_ArtinKP_T_hasResOn_kubota_aSer
-- name    : ArtinKP.T.hasResOn_kubota_aSer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:42.440195+00:00
-- url     : https://prove2.me/theorems/b5d17b84-17d4-4d7e-9050-5bb33a5a070a
-- title:
--   ArtinKP.T.hasResOn_kubota_aSer: the Kubota Dirichlet series continues to the slit half-plane and has residue τ_Φ(ν) at s = 4/3 along the ray
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume $F$ is totally complex, `ArtinKP.A.Good` $\mathfrak m$, and that $\mathcal O_F$ contains a primitive sixth root of unity $z_6$; let $P$ be a cubic symbol package, $\Phi$ a genuine section (`ArtinKP.S.GSection` $\iota\,P\,\mathfrak m$) and $\nu\in R$ with $\nu\neq 0$. Let $\mathfrak a_\Phi(\nu,s)$ be the Kubota Dirichlet series `ArtinKP.E.Kubota.aSer` of the structure `ArtinKP.B.kubota`: the sum over the nonzero classes $a$ of $R$ modulo units of $g(\nu;c)\,\Lambda_\Phi(c,\nu,s)\,N(c)^{-s}$, $c$ the chosen representative of $a$ (Gauss sum of the exterior cubic residue symbol, normalized finite Jacquet factor of $\Phi$, and $N(c)=\#(R/cR)$; see `ArtinKP.B.summable_kTerm_of_two_lt_re`). The statement is `ArtinKP.E.HasResOn` with domain `ArtinKP.E.slit`, point $4/3$, curve $t\mapsto s_t=4/3+t(1+i)$ and value `ArtinKP.T.tau` $\Phi\,\nu$, that is: there is a function $A:\mathbb C\to\mathbb C$, analytic at every point of the slit half-plane $\Omega=\{s:\operatorname{Re}s>1\}\setminus(1,2]$, with $A(s)=\mathfrak a_\Phi(\nu,s)$ for every $s$ with $\operatorname{Re}s>2$, and
--   $$\lim_{t\to 0^+}\,(s_t-4/3)\,A(s_t)=\tau_\Phi(\nu).$$
--   Here $\tau_\Phi(\nu)$ is itself defined as a limit of this kind (`ArtinKP.T.resSlit` of the series: the limit along the ray of $(s_t-4/3)$ times a chosen holomorphic continuation to $\Omega$, with junk values when no continuation or no limit exists); the statement provides an analytic continuation along which that value is attained as the limit.
--
--   **Role in the argument.** It certifies $\tau_\Phi(\nu)$ as the residue at $s=4/3$, along the ray, of the analytically continued Kubota series. The Fourier coefficients of the cubic theta function are expressed through $\tau$ (see `ArtinKP.T.coeffFunctional_theta_twist_eq`), and Theorem E of the development evaluates $\tau$ (see `ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir`).
--
--   **The statement**, as published (namespace `ArtinKP.T`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem hasResOn_kubota_aSer (hν : ν ≠ 0) :
--       E.HasResOn E.slit (4 / 3) (fun t : ℝ => (4 / 3 : ℂ) + t * (1 + Complex.I))
--         ((kubota hG hz6).aSer Φ ν) (tau hG hz6 Φ ν)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B7.sAdd`, `ArtinKP.S.GSection` and `ArtinKP.S2.cubicSymbol` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.B.kubota`, `ArtinKP.E.HasResOn`, `ArtinKP.E.slit`, `ArtinKP.T.tau` and `ArtinKP.E.Kubota.aSer` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB016` of this split imports it.
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
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

theorem hasResOn_kubota_aSer (hν : ν ≠ 0) :
    E.HasResOn E.slit (4 / 3) (fun t : ℝ => (4 / 3 : ℂ) + t * (1 + Complex.I))
      ((kubota hG hz6).aSer Φ ν) (tau hG hz6 Φ ν) := by
  sorry

end

end ArtinKP.T
end
