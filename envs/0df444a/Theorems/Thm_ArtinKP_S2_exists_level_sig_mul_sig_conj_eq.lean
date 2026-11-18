-- Prove2me | Theorems.Thm_ArtinKP_S2_exists_level_sig_mul_sig_conj_eq
-- name    : ArtinKP.S2.exists_level_sig_mul_sig_conj_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:40.639202+00:00
-- url     : https://prove2.me/theorems/6ecea3a8-e12f-4025-b886-21be91ae80c0
-- title:
--   ArtinKP.S2.exists_level_sig_mul_sig_conj_eq: for σ ∈ SL₂(F), Kubota's σ_S satisfies the conjugation identity on a deep enough S_f-adic neighbourhood of 1
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume `ArtinKP.A.Good` $\mathfrak m$; $\iota$ and the cubic symbol package $P$ are arbitrary. For $x,y\in F$ write $\langle x,y\rangle$ = `ArtinKP.S.brk` $\iota\,P\,\mathfrak m\,x\,y$, which is $\iota$ of the $S$-Hilbert pairing $\prod_{v\supseteq\mathfrak m}h_v(x,y)$ when $x,y\neq 0$ and $1$ otherwise; write $X(c,d)=c$ if $c\ne 0$ and $X(c,d)=d$ if $c=0$ (`ArtinKP.S.Xs`). For a pair $p=(c,d)\in F^2$ and a matrix $k=\begin{pmatrix}a&b\\c'&d'\end{pmatrix}$, Kubota's $\sigma_S$ evaluated on them is
--   $$\mathrm{sig}(p,k)=\big\langle X(pk)/X(p),\ X(pk)/X(c',d')\big\rangle,\qquad pk=(ca+dc',\ cb+dd')$$
--   (`ArtinKP.S.sig`). The statement: let $\sigma=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$ with entries in $F$ and $\alpha\delta-\beta\gamma=1$. Then there is $N\in\mathbb N$ such that for every $k$ satisfying `ArtinKP.S.IsK` $\mathfrak m\,N$ (determinant $1$, and $a-1$, $b$, $c'$, $d'-1$ each of $v$-adic order at least $N$ at every prime $v\supseteq\mathfrak m$) and every pair $p=(c,d)\ne(0,0)$ in $F^2$,
--   $$\mathrm{sig}(p,\sigma)\,\mathrm{sig}(p\sigma,\ \sigma^{-1}k\sigma)=\mathrm{sig}(p,k)\,\mathrm{sig}(pk,\ \sigma).$$
--   The entries of $\sigma^{-1}k\sigma$ are written out in the statement as `ArtinKP.S2.cj00`, `ArtinKP.S2.cj01`, `ArtinKP.S2.cj10`, `ArtinKP.S2.cj11`. The level $N$ is chosen after $\sigma$ (with $\mathfrak m$, $\iota$ and $P$ fixed before it) and before $k$ and $p$.
--
--   **Role in the argument.** It is the symbol identity behind the level of a translated section: translating a genuine section by $\sigma$ preserves the level condition, with a new level.
--
--   **The statement**, as published (namespace `ArtinKP.S2`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S`):
--
--   ```lean
--   theorem exists_level_sig_mul_sig_conj_eq (hG : Good 𝔪) {α β γ δ : F} (det : α * δ - β * γ = 1) :
--       ∃ N : ℕ, ∀ a b c' d' : F, IsK 𝔪 N a b c' d' → ∀ c d : F, c ≠ 0 ∨ d ≠ 0 →
--         sig ι P 𝔪 c d α β γ δ * sig ι P 𝔪 (c * α + d * γ) (c * β + d * δ)
--             (cj00 α β γ δ a b c' d') (cj01 α β γ δ a b c' d') (cj10 α β γ δ a b c' d')
--             (cj11 α β γ δ a b c' d')
--           = sig ι P 𝔪 c d a b c' d' * sig ι P 𝔪 (c * a + d * c') (c * b + d * d') α β γ δ
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.IsK` and `ArtinKP.S.sig` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.S2.cj00`, `ArtinKP.S2.cj01`, `ArtinKP.S2.cj10` and `ArtinKP.S2.cj11` (definitions bundle `ArtinKPB004` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB016` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
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
import Definitions.Def_ArtinKPB004

section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem exists_level_sig_mul_sig_conj_eq (hG : Good 𝔪) {α β γ δ : F} (det : α * δ - β * γ = 1) :
    ∃ N : ℕ, ∀ a b c' d' : F, IsK 𝔪 N a b c' d' → ∀ c d : F, c ≠ 0 ∨ d ≠ 0 →
      sig ι P 𝔪 c d α β γ δ * sig ι P 𝔪 (c * α + d * γ) (c * β + d * δ)
          (cj00 α β γ δ a b c' d') (cj01 α β γ δ a b c' d') (cj10 α β γ δ a b c' d')
          (cj11 α β γ δ a b c' d')
        = sig ι P 𝔪 c d a b c' d' * sig ι P 𝔪 (c * a + d * c') (c * b + d * d') α β γ δ := by
  sorry

end ArtinKP.S2
end
end
