-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:30:51.053079+00:00
-- url     : https://prove2.me/theorems/6a531877-6086-4354-9807-308eafa2a643
-- title:
--   Goldmakher–Louvel's functional equation for ζ_𝔪 · L(χ_{c₁}χ_{c₂}) for the exterior quadratic symbols χ_c(𝔞)³ of OpenAI's Primitive roots paper, with conductor c₁c₂ and root number 1
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). Write $\chi_{\mathfrak c}(\mathfrak a)$ for `residueSymbol ι 𝔪 𝔞 (g.gen 𝔠) ^ 3` (bundle `Def_ArtinHeckeTheta`), $q_{\mathfrak a}$ for the absolute norm and $r_2$ for the number of complex places of $F$. There exist a natural number $k$ and a map `cls` from the ideals of $\mathcal O_F$ to `Fin k` (both existential, and allowed to depend on $\mathfrak m$ and $g$) such that for all ideals $\mathfrak g, \mathfrak c_1, \mathfrak c_2$ with $\mathfrak g\mathfrak c_1\mathfrak c_2$ exterior (`IsExterior 𝔪`) and squarefree, $\mathfrak c_1\mathfrak c_2 \ne \mathcal O_F$ and `cls (𝔤 * c₁) = cls (𝔤 * c₂)`, there is an entire function $\Lambda$ with:
--
--   1. for $\operatorname{Re} w > 1$,
--   $$\Lambda(w) = \prod_{P \mid \mathfrak m}\big(1 - q_P^{-w}\big)^{-1} \sum_{\mathfrak a\ \text{exterior}} \chi_{\mathfrak c_1}(\mathfrak a)\,\chi_{\mathfrak c_2}(\mathfrak a)\, q_{\mathfrak a}^{-w},$$
--   the product over the prime factors of $\mathfrak m$;
--   2. for every $w$ with neither $w$ nor $1 - w$ in $\{0, -1, -2, \dots\}$,
--   $$\big(|d_F|\, q_{\mathfrak c_1\mathfrak c_2}\big)^{w/2}\,\Gamma_{\mathbb C}(w)^{r_2}\,\Lambda(w) = \big(|d_F|\, q_{\mathfrak c_1\mathfrak c_2}\big)^{(1-w)/2}\,\Gamma_{\mathbb C}(1-w)^{r_2}\,\Lambda(1-w),$$
--   with $\Gamma_{\mathbb C}$ = `Complex.Gammaℂ` and complex powers taken with the principal branch;
--   3. for all real $\sigma_1, \sigma_2$ there are $C$ and $A$ with $|\Lambda(w)| \le C(1 + |\operatorname{Im} w|)^A$ for $\sigma_1 \le \operatorname{Re} w \le \sigma_2$.
--
--   This is the input that L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, take from Hecke theory in §6 for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. In their terms, $\chi_{\mathfrak c_1}\chi_{\mathfrak c_2}$ is the quadratic Hecke character of $F(\sqrt{c_1c_2})$, with $c_i$ = `g.gen 𝔠ᵢ`; `cls` is their class map $[\cdot]$ to the finite group $G$ of property (2) of their Definition 1, and property (3) makes the character primitive of conductor $\mathfrak c_1\mathfrak c_2$ when $[\mathfrak g\mathfrak c_1] = [\mathfrak g\mathfrak c_2]$. Their functional equation (3.1) has root number $\epsilon(\chi) = 1$ for a quadratic character. The product over $P \mid \mathfrak m$ restores the Euler factors at the primes dividing $\mathfrak m$, which the sum over exterior ideals leaves out. In §6.2–6.3 they use this functional equation for the explicit formula for $\Sigma_3$.
--
--   It is a cut for `exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le` (their Proposition 5.2).
--
--   Goldmakher–Louvel, (3.1): “Any primitive ray class character χ (mod f) over k (i.e. a Hecke character of trivial infinite type) satisfies the functional equation Λ(χ, s) = ǫ(χ)(N f)^{1/2−s} Λ(1 − s, χ) … Moreover, if the character χ is quadratic, we know that ǫ(χ) = 1.” and §6.3: “Recall that the conductor of χ_{b1} χ_{b2} is precisely b1 b2 in this case.”
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, (3.1) with ε(χ) = 1 and Definition 1 (3), as used in §6 (the functional equation of ζ_𝔪 · L(χ_{c₁}χ_{c₂}), conductor c₁c₂; a cut for Proposition 5.2, for the family of Lemma 6.4 of OpenAI, Primitive roots for every admissible integer base, p. 38)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
        ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) → Squarefree (𝔤 * c₁ * c₂) →
          c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ w : ℂ, 1 < w.re →
              Λ w = (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔪).toFinset,
                  (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
                ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞},
                  residueSymbol ι 𝔪 𝔞.1 (g.gen c₁) ^ 3 * residueSymbol ι 𝔪 𝔞.1 (g.gen c₂) ^ 3 *
                    (Ideal.absNorm 𝔞.1 : ℂ) ^ (-w)) ∧
            (∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
              (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ (w / 2) *
                  Complex.Gammaℂ w ^ InfinitePlace.nrComplexPlaces F * Λ w =
                (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ ((1 - w) / 2) *
                  Complex.Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w)) ∧
            (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
              ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A) := by
  sorry

end ArtinPrimitiveRoots
