-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_principalCoeff_prime_pow_mul_eq_mul
-- name    : ArtinPrimitiveRoots.exists_cutoff_principalCoeff_prime_pow_mul_eq_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T16:05:33.88133+00:00
-- url     : https://prove2.me/theorems/a049f077-284c-47e9-b5b5-f711e912b44e
-- title:
--   (7.16) of OpenAI's Primitive roots paper, at u = 1 — the principal coefficients factor across primes
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). Put
--   $$b(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r) = \gamma_2(\mathfrak c)\,\vartheta(\mathfrak c\mathfrak n^3)\,F\bigl(\mathfrak s, \mathfrak c\mathfrak n^3, g(\mathfrak r)^6\bigr),$$
--   with $\gamma_2$ = `gaussPhase g 2`, $\vartheta$ = `χ.thetaChar g` and $F$ = `poissonFactor g` (bundle `Def_ArtinHeckeTheta`). Then for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`), all $e_0 \le 1$ and $l, k, m \ge 0$, and all ideals $\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r$ coprime to $\mathfrak m$ and not contained in $P$, with $\mathfrak c$ squarefree,
--   $$b(P^{e_0}\mathfrak c, P^l\mathfrak n, P^k\mathfrak s, P^m\mathfrak r) = b(P^{e_0}, P^l, P^k, P^m)\,b(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r).$$
--
--   This is the cross-prime part of (7.16) for the row $u = 1$ of (7.11): the Chinese-remainder twists of $F$ and of $\gamma_2$ cancel by the reciprocity (3.3) of allowed generators. It was checked numerically in $\mathbb Q(\zeta_{12})$ with $S$ the primes above $2$ and $3$, four exterior primes of norms $13, 13, 37, 61$ and generators chosen to satisfy (3.3) exactly, over about $10^5$ cases with no failure; breaking (3.3) for one generator makes it fail. With the local values (7.17) and the identities of Lemma 3.4 it is a cut for `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 48: “Thus all cross-prime terms cancel, including when both moduli have powers of the same primes; those shared powers were retained inside Equation (7.15). […] It follows initially by absolute convergence that $\mathcal F_u = \prod_{\mathfrak p \notin S} \mathcal F_{u,\mathfrak p}$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 47–48, proof of Proposition 7.3, (7.16) at u = 1 (cancellation of the cross-prime terms)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_principalCoeff_prime_pow_mul_eq_mul (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let b : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            b (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              b (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * b 𝔠 𝔫 𝔰 𝔯 := by
  sorry

end ArtinPrimitiveRoots
