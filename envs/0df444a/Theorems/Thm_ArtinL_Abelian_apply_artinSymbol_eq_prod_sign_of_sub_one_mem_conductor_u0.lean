-- Prove2me | Theorems.Thm_ArtinL_Abelian_apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0
-- name    : ArtinL.Abelian.apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/583e332c-400b-5788-946a-b4c7a79b8042
-- title:
--   Sign formula for the Artin symbol of (α)
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois and with abelian Galois group $\mathrm{Gal}(L/K) = L \simeq_{\mathrm{alg}[K]} L$, and let $\psi \colon \mathrm{Gal}(L/K) \to \mathbb{C}^\times$ be a group homomorphism. Let $\mathfrak{m}$ be an ideal of $\mathcal{O}_K$ and let $\alpha \in \mathcal{O}_K$ be non-zero. Two hypotheses are imposed on $\alpha$: first, the invertible fractional ideal $(\alpha) = \mathrm{span}\{\alpha\}$ lies in the subgroup `coprimeToModulus K 𝔪`, that is, its $v$-adic count vanishes for every height-one prime $v$ of $\mathcal{O}_K$ whose ideal divides $\mathfrak{m}$; second, $\alpha - 1$ lies in the ideal [`ArtinL.Abelian.conductor ψ`](def/ArtinL_Abelian.html#L57), the finite product $\prod_v v^{e_v}$ over height-one primes with exponent $e_v = (1$ unless $\psi$ is unramified at $v$, in which case $0) + \lceil \mathrm{swanConductor}\,\psi\,v \rceil$. The conclusion is an identity in $\mathbb{C}$: the value of $\psi$ on $\mathrm{artinSymbol}\,K\,L\,\mathfrak{m}$ applied to $(\alpha)$ together with its coprimality witness — the ray-class Artin map built from the arithmetic Frobenius elements `artinFrob K L v` at the primes of $\mathcal{O}_L$ above $v$ — equals the product, over those real infinite places $w$ of $K$ for which [`ArtinL.Abelian.IsPlusAt ψ w`](def/ArtinL_Abelian.html#L66) fails (i.e. for which some infinite place of $L$ restricting to $w$ has an element of its stabiliser in $\mathrm{Gal}(L/K)$ on which $\psi$ is not $1$), of the sign of the image of $\alpha$ under the real embedding attached to $w$, viewed as an integer and then as a complex number.
--
--   This is the sign-refined form of Artin reciprocity for a character of a finite abelian extension: for $\alpha$ congruent to $1$ modulo the Artin conductor of $\psi$, the character value on the Artin symbol of the principal ideal $(\alpha)$ is determined purely by the archimedean behaviour of $\alpha$ at the real places where $\psi$ is non-trivial on a decomposition group at infinity. It is used in the construction of a narrow ray class character with prescribed conductor and prescribed local values, via [`ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0`](thm.html#ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin

open scoped Classical in

theorem ArtinL.Abelian.apply_artinSymbol_eq_prod_sign_of_sub_one_mem_conductor_u0
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔪 : Ideal (𝓞 K)) (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪)
    (h1 : α - 1 ∈ ArtinL.Abelian.conductor ψ) :
    ((ψ (artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩) : ℂˣ) : ℂ) =
      ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
          ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
        ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ) := by sorry
