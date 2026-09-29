-- Prove2me | Theorems.Thm_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_conductor_lt_u0
-- name    : ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_conductor_lt_u0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0cabdb95-4f9b-50e4-9da9-5443c3098618
-- title:
--   Minimality of the conductor of an abelian character
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois, with commutative Galois group $L \simeq_{\mathrm{alg}[K]} L$, and let $\psi \colon \mathrm{Gal}(L/K) \to \mathbb{C}^\times$ be a monoid homomorphism. Write $\mathfrak{f} =$ [`ArtinL.Abelian.conductor`](def/ArtinL_Abelian.html#L57) $\psi$ for the ideal $\prod_v v^{e_v}$ of $\mathcal{O}_K$, the finitary product over the height-one primes $v$ of $\mathcal{O}_K$ with exponent $e_v = (1$ if $\psi$ is not unramified at $v$, else $0) + \lceil \mathrm{sw}(\psi, v) \rceil$, the Swan contribution rounded up. Let $\mathfrak{f}'$ be an ideal of $\mathcal{O}_K$ with $\mathfrak{f} \subseteq \mathfrak{f}'$ and $\mathfrak{f}' \neq \mathfrak{f}$, that is, a proper divisor of the conductor. Then there exists $\alpha \in \mathcal{O}_K$, $\alpha \neq 0$, such that the principal fractional ideal $(\alpha)$ lies in `coprimeToModulus` $K\,\mathfrak{f}$, i.e. its $v$-adic count vanishes at every height-one prime $v$ dividing $\mathfrak{f}$, and such that $\alpha - 1 \in \mathfrak{f}'$, $\alpha$ is totally positive ($\tau(\alpha) > 0$ for every ring homomorphism $\tau \colon K \to \mathbb{R}$), and $\psi$ of the Artin symbol of $(\alpha)$ at modulus $\mathfrak{f}$ — the multiplicative extension to ideals coprime to $\mathfrak{f}$ of $v \mapsto$ the arithmetic Frobenius at a prime of $L$ above $v$ — is different from $1$.
--
--   This is the minimality half of the identification of the Artin conductor of an abelian character with the conductor of the associated ray class character: $\psi$ composed with the Artin symbol is trivial on the ray modulo $\mathfrak{f}(\psi)$ but not on the ray modulo any strictly larger ideal. It is used in the construction of a narrow ray class character whose conductor equals the Artin conductor, within the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_conductor_lt_u0.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin

theorem ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_conductor_lt_u0
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔣' : Ideal (𝓞 K)) (hle : ArtinL.Abelian.conductor ψ ≤ 𝔣') (hne : 𝔣' ≠ ArtinL.Abelian.conductor ψ) :
    ∃ (α : 𝓞 K) (hα : α ≠ 0)
      (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
      α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
        ψ (artinSymbol K L (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) ≠ 1 := by sorry
