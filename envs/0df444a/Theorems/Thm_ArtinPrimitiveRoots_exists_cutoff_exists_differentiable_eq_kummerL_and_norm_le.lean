-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T20:49:16.885533+00:00
-- url     : https://prove2.me/theorems/8ad1a151-a30e-4f5a-8afc-0dd78f4a1cc8
-- title:
--   (8.14) of OpenAI's Primitive roots paper — for u ≠ 1, L^S(w, χ•(u)) is entire and O(q_u^{1/2+ε}(2 + |Im w|)^A) on .003 ≤ Re w ≤ 4
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). There is $A$ such that for every $\varepsilon > 0$ there is $C$ with the following property: for every frequency class $r \ne$ `principalFreq 𝔪`, with $u$ = `freqElt g r` and $q_u$ the norm of $r.1$, there is an entire function $\Lambda$ equal to `kummerL ι 𝔪 u w` $= L^S(w, \chi_\bullet(u))$ for $\operatorname{Re} w > 1$ and satisfying $|\Lambda(w)| \le C q_u^{1/2+\varepsilon}(2 + |\operatorname{Im} w|)^A$ for $.003 \le \operatorname{Re} w \le 4$.
--
--   This is (8.14), the input from Lemma 3.3 (the Kummer characters $\chi_\bullet(u)$ and their conductors) and the convexity bound (8.3). The paper states it on the dyad $U \le q_u < 2U$ with $U^{1/2+\epsilon}$, which is the same as $q_u^{1/2+\epsilon}$ up to a constant; the exponent $A$ is the paper's $A_F$. The constant may depend on $\mathfrak m$, $g$ and $\varepsilon$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 56: “The numerator for each of these rows is entire. From Equation (8.3) and the omitted-factor bound, $L^S(w, \chi_\bullet(u)) \ll_\epsilon U^{1/2+\epsilon}(2 + |\operatorname{Im} w|)^{A_F}$ $(.003 \le \operatorname{Re} w \le 4)$. (8.14)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 56, (8.14) (Lemma 3.3 and the convexity bound (8.3))

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ A : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
          (∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 (freqElt g r) w) ∧
          ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
            ‖Λ w‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |w.im|) ^ A := by
  sorry

end ArtinPrimitiveRoots
