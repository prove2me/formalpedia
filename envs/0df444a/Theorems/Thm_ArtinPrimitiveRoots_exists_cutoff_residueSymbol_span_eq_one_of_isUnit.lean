-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_residueSymbol_span_eq_one_of_isUnit
-- name    : ArtinPrimitiveRoots.exists_cutoff_residueSymbol_span_eq_one_of_isUnit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T13:06:32.3395+00:00
-- url     : https://prove2.me/theorems/3b83b5af-dda3-40a1-9eb4-915e3c4d3438
-- title:
--   Lemma 3.3 of OpenAI's Primitive roots paper for S-units — χ_(α)(u) = 1 for α ≡ 1 mod 𝔪^j
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ with the following property. Take a nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), a system of allowed generators (`AllowedGen ι 𝔪`), and a unit $u$ of the $S$-integers $R$ (`SInt 𝔪`). Then there is $j \ge 0$ such that $\chi_{(\alpha)}(u) = 1$ (`residueSymbol ι 𝔪 (Ideal.span {α}) u = 1`) for every $\alpha \in \mathcal O_F$ with $\alpha - 1 \in \mathfrak m^j$.
--
--   This is a cut for `exists_cutoff_prod_gaussPhase_three_span_eq_one`; that reduction is proved in Lean.
--
--   In the paper this is Lemma 3.3 (pp. 11–12): the ideal function $\chi_\bullet(u)$ is induced, away from $S$ and the prime divisors of $u$, by a finite-order Hecke character whose conductor is supported on $S$ when $u$ is an $S$-unit.
--
--   **Formalization note.** "Induced by a Hecke character with conductor in $S$" is stated through its values on principal ideals $(\alpha)$, $\alpha \equiv 1 \pmod{\mathfrak m^j}$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 11–12, Lemma 3.3 for S-units u (χ_•(u) is induced by a Hecke character with conductor supported on S, so χ_(α)(u) = 1 for α ≡ 1 mod 𝔪^j); a cut for exists_cutoff_prod_gaussPhase_three_span_eq_one

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_residueSymbol_span_eq_one_of_isUnit (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
      residueSymbol ι 𝔪 (Ideal.span {α}) u = 1
  := by
  sorry

end ArtinPrimitiveRoots
