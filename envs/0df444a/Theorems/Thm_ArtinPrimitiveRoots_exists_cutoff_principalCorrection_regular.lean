-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_principalCorrection_regular
-- name    : ArtinPrimitiveRoots.exists_cutoff_principalCorrection_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T10:47:00.465286+00:00
-- url     : https://prove2.me/theorems/e5b31770-e0f9-467c-9b4a-707c0d16ebf8
-- title:
--   Proposition 7.3, u = 1, of OpenAI's Primitive roots paper — the principal correction ℋ_η is holomorphic, nowhere zero and bounded on Re s > .998 once S contains the small primes
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that for every ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, the principal correction $\mathcal H(s) = $ `χ.principalCorrection ι s` is holomorphic on $\{\operatorname{Re} s > 998/1000\}$, has no zeros there, and is bounded there: some $B$ has $|\mathcal H(s)| \le B$ for all $s$ with $\operatorname{Re} s > 998/1000$.
--
--   The bundle `Def_ArtinHeckeProbe` defines $\mathcal H$ as the product over the primes $P \nmid \mathfrak m$ of the closed form of the paper's local factor $\mathcal H_{1,\mathfrak p}(s, 1, 1/6)$. The open half-plane $\operatorname{Re} s > .998$ is contained in the paper's open neighbourhood of $\operatorname{Re} s \ge .998$. $N_0$ depends on $F$ (and $\iota$) only, as the paper's “sufficiently large fixed constant” does.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 46, Proposition 7.3: “The correction $\mathcal H_u$ is holomorphic in open neighborhoods of both real-part regions [(7.13)] […] If $S$ contains every prime of norm at most a sufficiently large fixed constant, then $\mathcal H_1$ is bounded and nowhere zero on both neighborhoods.” and p. 50: “For the remainder of the proof, write $\mathcal H_\eta(s) := \mathcal H_1(s, 1, 1/6)$. This is the principal specialization announced in Section 4. Since $(w, z) = (1, 1/6)$ lies in the second region of Equation (7.13), $\mathcal H_\eta$ is holomorphic, bounded, and nowhere zero on an open neighborhood of the closed half-plane $\operatorname{Re} s \ge .998$, uniformly in height.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46, 50, Proposition 7.3, the case u = 1 (ℋ_η holomorphic, bounded and nowhere zero)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_principalCorrection_regular (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), SmallPrimesDvd N₀ 𝔪 → ∀ χ : HeckeChar F 𝔪,
      DifferentiableOn ℂ (χ.principalCorrection ι) {s | 998 / 1000 < s.re} ∧
      (∀ s : ℂ, 998 / 1000 < s.re → χ.principalCorrection ι s ≠ 0) ∧
      ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖χ.principalCorrection ι s‖ ≤ B := by
  sorry

end ArtinPrimitiveRoots
