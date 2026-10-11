-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal
-- name    : ArtinPrimitiveRoots.exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T16:05:47.50795+00:00
-- url     : https://prove2.me/theorems/147b7f32-4e9e-4d75-a5a7-084c5dba215d
-- title:
--   (7.17) of OpenAI's Primitive roots paper, at u = 1 — the Poisson factor at a prime power
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`): for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`), all $e_0 \le 1$ and all $l, k, m \ge 0$,
--   $$F\bigl(P^k, P^{e_0}(P^l)^3, g(P^m)^6\bigr) = \texttt{poissonLocal}\bigl(NP, \gamma_1(P), e_0, l, k, m\bigr),$$
--   with $F$ = `poissonFactor g` and $\gamma_1$ = `gaussPhase g 1` (bundle `Def_ArtinHeckeTheta`) and `poissonLocal` from `Def_ArtinHeckePoissonLocal`.
--
--   This is (7.17) for the row $u = 1$, at $t = e_0 + 3l$ and $J = 6m$, where the unit multiplier (7.14) is trivial. It was checked numerically in $\mathbb Q(\zeta_{12})$ at primes of norms $13, 37, 61$ with $e_0 \le 1$, $l \le 4$, $k \le 2$, $m \le 3$ (480 cases, no failure). With (7.16) and the identities of Lemma 3.4 it is a cut for `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 48: “For $t = 0$ the value is $C_{0,0}(J) = 1$, and $C_{0,k}(J) = \mathbf 1_{J=0}$ for $k > 0$. For $t > 0$ it is $C_{t,0}(J) = \mathbf 1_{J \ge t-1} Q^{t-1} T_t(p^{J-t+1})$, $C_{t,1}(J) = \mathbf 1_{J\ge t}\,\tau_1 Q^{t-1} T_{t-1}(p^{J-t})$, $C_{t,k}(J) = 0$ $(k \ge 2)$. (7.17)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 47–48, proof of Proposition 7.3, (7.15)–(7.17) at u = 1 (the Poisson factor at a prime power)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckePoissonLocal

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
        poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) =
          poissonLocal (Ideal.absNorm P) (gaussPhase g 1 P) e₀ l k m := by
  sorry

end ArtinPrimitiveRoots
