-- Prove2me | Theorems.Thm_ArtinKP_A_kappa_mul_of_mem_Gamma
-- name    : ArtinKP.A.kappa_mul_of_mem_Gamma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:16:06.593358+00:00
-- url     : https://prove2.me/theorems/75718ed3-ae02-4ffd-bf5b-df3ca16e1644
-- title:
--   ArtinKP.A.kappa_mul_of_mem_Gamma: the Kubota symbol κ is multiplicative on Γ(𝔫) when 𝔫 ⊆ 𝔪^N for a deep level N ≥ 1
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field, $\mathfrak m$ an ideal of $\mathcal O_F$, $S_f$ the set of primes of $\mathcal O_F$ containing $\mathfrak m$, and $R$ = `ArtinPrimitiveRoots.SInt` $\mathfrak m$ the ring of elements of $F$ integral at every prime outside $S_f$; a prime not in $S_f$ is called exterior. $\iota : F\to\mathbb C$ is a ring homomorphism. `ArtinKP.A.Good` $\mathfrak m$ says: $\mathfrak m\ne 0$, every prime containing $6$ contains $\mathfrak m$, and every ideal of $\mathcal O_F$ generates a principal ideal of $R$. A cubic symbol package $P$ (`ArtinKP.A.CubicPkg` $F$) is a family of bimultiplicative pairings $h_v : F^\times\times F^\times\to\mu_3(F)$, one for each prime $v$, satisfying the Steinberg relation, a product formula, triviality on pairs of units at primes not dividing $3$, a tame formula at those primes, and local constancy. The exterior cubic residue symbol $(d/c)$ = `ArtinKP.A.cubicExt` $\iota\,\mathfrak m\,d\,c$ of $c,d\in R$ is $\prod_v\chi_v(d)^{2\,\mathrm{ord}_v(c)}$ over the exterior primes $v$ at which $c$ is not a unit, with $\chi_v$ the sextic residue symbol `ArtinPrimitiveRoots.sexticResidueSymbol` (value in $\mathbb C$ through $\iota$, and $0$ when $d\in vR$); it is $1$ when $c=0$.
--
--   **In words.** Assume `ArtinKP.A.Good` $\mathfrak m$, a cubic symbol package $P$, and a primitive sixth root of unity $z_6\in\mathcal O_F$. Let $N\ge 1$ be a deep level of $P$ for $\mathfrak m$ (`ArtinKP.A.CubicPkg.IsDeepLevel`: for every prime $v\supseteq\mathfrak m$ and all $a,b\in F^\times$, $h_v(a,b)=1$ as soon as $b-1$ has $v$-adic order at least $N$), and let $\mathfrak n$ be an ideal of $\mathcal O_F$ with $\mathfrak n\subseteq\mathfrak m^N$. Let $\Gamma(\mathfrak n)$ = `ArtinKP.A.Gamma` $\mathfrak m\,\mathfrak n$ be the image in $\mathrm{SL}_2(R)$ of the kernel of reduction $\mathrm{SL}_2(\mathcal O_F)\to\mathrm{SL}_2(\mathcal O_F/\mathfrak n)$. Then for all $\gamma_1,\gamma_2\in\Gamma(\mathfrak n)$,
--   $$\kappa(\gamma_1\gamma_2)=\kappa(\gamma_1)\,\kappa(\gamma_2),$$
--   where $\kappa$ = `ArtinKP.A.kappa` $\iota\,\mathfrak m$ is the Kubota symbol on $\mathrm{SL}_2(R)$: $\kappa\begin{pmatrix}a&b\\c&d\end{pmatrix}=1$ if $c=0$ and $(d/c)^{-1}$ otherwise. The symbol $\kappa$ itself does not involve $P$; the package enters only through the deep-level hypothesis.
--
--   **Role in the argument.** It makes $\kappa$ a character of the congruence subgroup $\Gamma(\mathfrak n)$; the genuine sections, the Eisenstein series and the cubic theta function of the development are built on this multiplier.
--
--   **The statement**, as published (namespace `ArtinKP.A`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix`):
--
--   ```lean
--   theorem kappa_mul_of_mem_Gamma (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
--       (hz6 : IsPrimitiveRoot z6 6) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N)
--       {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≤ 𝔪 ^ N) {γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)}
--       (h₁ : γ₁ ∈ Gamma 𝔪 𝔫) (h₂ : γ₂ ∈ Gamma 𝔪 𝔫) :
--       kappa ι 𝔪 (γ₁ * γ₂) = kappa ι 𝔪 γ₁ * kappa ι 𝔪 γ₂
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Gamma`, `ArtinKP.A.Good`, `ArtinKP.A.kappa` and `ArtinKP.A.CubicPkg.IsDeepLevel` (definitions bundle `ArtinKPB000` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB015` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB000

section

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

theorem kappa_mul_of_mem_Gamma (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N)
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≤ 𝔪 ^ N) {γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)}
    (h₁ : γ₁ ∈ Gamma 𝔪 𝔫) (h₂ : γ₂ ∈ Gamma 𝔪 𝔫) :
    kappa ι 𝔪 (γ₁ * γ₂) = kappa ι 𝔪 γ₁ * kappa ι 𝔪 γ₂ := by
  sorry

end ArtinKP.A
end
end
