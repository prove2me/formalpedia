-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul
-- name    : ArtinPrimitiveRoots.exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T15:07:21.550413+00:00
-- url     : https://prove2.me/theorems/8a9ce98d-2487-4fc9-81eb-0a95e7b4cf14
-- title:
--   Proposition 7.3 (7.16)–(7.17) of OpenAI's Primitive roots paper, at u = 1 — the principal coefficients are normalized and multiplicative prime by prime
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). Put
--   $$a(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r) = \gamma_2(\mathfrak c)\,\vartheta(\mathfrak c\mathfrak n^3)\,F\bigl(\mathfrak s, \mathfrak c\mathfrak n^3, u\cdot g(\mathfrak r)^6\bigr),$$
--   with $\gamma_2$ = `gaussPhase g 2`, $\vartheta$ = `χ.thetaChar g`, $F$ = `poissonFactor g`, and $u$ = `freqElt g (principalFreq 𝔪)` the principal frequency (all from the bundle `Def_ArtinHeckeTheta`). Then:
--   1. $a(1, 1, 1, 1) = 1$;
--   2. for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`), all $e_0 \le 1$ and $l, k, m \ge 0$, and all ideals $\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r$ coprime to $\mathfrak m$ and not divisible by $P$, with $\mathfrak c$ squarefree:
--   $$a(P^{e_0}\mathfrak c, P^l\mathfrak n, P^k\mathfrak s, P^m\mathfrak r) = c_P(e_0, l, k, m)\,a(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r),$$
--   where $c_P$ = `principalLocalCoeff` $(NP, \chi(P), \overline{\texttt{jacobiPhaseSix}\ \iota\ P}\,\chi(P)^6)$ (bundles `Def_ArtinHeckeLocalCoeff` and `Def_ArtinHeckeProbe`).
--
--   These are the multiplicativity (7.16) and the local values (7.17) of the coefficients of $\mathcal F_1$, the row $u = 1$ of (7.11). The principal frequency is a sixth power of an $S$-unit, and $F$ is unchanged when its frequency is multiplied by one, because $6 \mid NP - 1$ at every prime outside $S$ ($\mu_{12} \subset F$). The values (7.17)–(7.19) were checked numerically at one prime ($Q = 13$); the cross-prime multiplicativity (7.16) has not been checked numerically. It is a cut for `exists_cutoff_freqSeries_principalFreq_eq` ((7.12) at $u = 1$).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 46, Proposition 7.3: “For every $u \in U$, the series in Equation (7.11) has the Euler factorization […] (7.12) initially in absolute convergence.” The proof, pp. 46–48, computes the coefficients prime by prime, (7.16)–(7.17).
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46–48, Proposition 7.3, (7.16)–(7.17) at u = 1 (normalization and prime-by-prime multiplicativity of the principal coefficients)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g (principalFreq 𝔪) * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m * a 𝔠 𝔫 𝔰 𝔯 := by
  sorry

end ArtinPrimitiveRoots
