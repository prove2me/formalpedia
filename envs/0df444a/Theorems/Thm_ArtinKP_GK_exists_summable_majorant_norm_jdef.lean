-- Prove2me | Theorems.Thm_ArtinKP_GK_exists_summable_majorant_norm_jdef
-- name    : ArtinKP.GK.exists_summable_majorant_norm_jdef
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:54:29.229165+00:00
-- url     : https://prove2.me/theorems/93186d12-c7b0-4573-8ca9-655796a879fc
-- title:
--   ArtinKP.GK.exists_summable_majorant_norm_jdef: the function J of a genuine section has a majorant summable against |y|^σ for every σ > −1/3
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume $F$ is totally complex, `ArtinKP.A.Good` $\mathfrak m$, and that $\mathcal O_F$ contains a primitive sixth root of unity $z_6$; let $P$ be a cubic symbol package. For $k\in\mathbb N$, `ArtinPrimitiveRoots.SFin` $\mathfrak m\,k$ is the group $F^\times/U_k$, where $U_k$ consists of the $x\in F^\times$ with $|x-1|_v\le N(v)^{-(k+1)}$ at every prime $v\supseteq\mathfrak m$; `ArtinPrimitiveRoots.SFinCls` $\mathfrak m\,k$ is its quotient by sixth powers; and for $y\in$ SFin, $|y|$ (`ArtinPrimitiveRoots.SFin.norm`) is $\prod_{v\supseteq\mathfrak m}|x|_v$ for any representative $x$. For a genuine section $\Phi_0$ (`ArtinKP.S.GSection` $\iota\,P\,\mathfrak m$), `ArtinKP.GK.Jdef` is the function
--   $$J(\mathrm{cl},y')=(-1)^{r}\,\langle\tilde\nu,\eta'\rangle\;\xi_{w\Phi_0}(\eta'),$$
--   with $r$ the number of infinite places, $\tilde\nu$ and $\eta'$ chosen representatives in $F^\times$ of $\mathrm{cl}$ and $y'$, $\langle\cdot,\cdot\rangle$ the $S$-Hilbert pairing read through $\iota$ (`ArtinKP.S.brk`), and $\xi_{w\Phi_0}$ (`ArtinKP.G1.xi`, taken for the theta functional `ArtinKP.T.theta`) the function $\xi_\Phi(\beta)=|\beta|_{S_f}^{1/3}\,\mathcal K_\Phi(\beta)$ of the Weyl-reflected section $\Phi=w\Phi_0$ (`ArtinKP.G1.wSec`), where the Kirillov function $\mathcal K_\Phi(\beta)$ is, for $\beta\neq 0$, the coefficient $\tau$ at $1$ of the translate of $\Phi$ by the torus element of $\beta$, and $0$ at $\beta=0$.
--
--   The statement: for every genuine section $\Phi_0$ and every $k\in\mathbb N$ there is a function $b : \mathrm{SFin}(\mathfrak m,k)\to\mathbb R$ such that
--
--   - $\|J(\mathrm{cl},y)\|\le b(y)$ for every class $\mathrm{cl}\in\mathrm{SFinCls}(\mathfrak m,k)$ and every $y$, and
--   - for every real $\sigma>-1/3$ the family $y\mapsto b(y)\,|y|^{\sigma}$ (real power) is summable over $\mathrm{SFin}(\mathfrak m,k)$.
--
--   **Role in the argument.** In the reflected expansion of the theta function the coefficients at the places of $S_f$ are values of $J$; this majorant, with its exponent $-1/3$, is the summable bound the goal requires of them. The proof of the section-level cut `ArtinKP.GR.secCut_of_isCyclotomicExtension`, from which the goal follows, imports the statement.
--
--   **The statement**, as published (namespace `ArtinKP.GK`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.B7`):
--
--   ```lean
--   theorem exists_summable_majorant_norm_jdef (Φ₀ : GSection ι P 𝔪) (k : ℕ) :
--       ∃ bf : SFin 𝔪 k → ℝ,
--         (∀ (cl : SFinCls 𝔪 k) (y : SFin 𝔪 k), ‖Jdef hG hz6 Φ₀ cl y‖ ≤ bf y) ∧
--         ∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 k => bf y * SFin.norm y ^ σ)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.GK.Jdef` (definitions bundle `ArtinKPB016` of this split).
--
--   **Used by.** The proof of `ArtinKP.GR.secCut_of_isCyclotomicExtension` and the definitions bundle `ArtinKPB017` of this split import it.
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
import Definitions.Def_ArtinKPB016

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {k : ℕ}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

theorem exists_summable_majorant_norm_jdef (Φ₀ : GSection ι P 𝔪) (k : ℕ) :
    ∃ bf : SFin 𝔪 k → ℝ,
      (∀ (cl : SFinCls 𝔪 k) (y : SFin 𝔪 k), ‖Jdef hG hz6 Φ₀ cl y‖ ≤ bf y) ∧
      ∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 k => bf y * SFin.norm y ^ σ) := by
  sorry

end

end ArtinKP.GK
end
