-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:24:32.043539+00:00
-- url     : https://prove2.me/theorems/926b5d87-7371-4d19-9e88-76bbdf0d9a96
-- title:
--   (8.14) of OpenAI's Primitive roots paper for every u that is not a sixth power — L^S(w, χ•(u)) is entire and O(N𝔟^{1/2+ε}(1 + |Im w|)^A) on 0 ≤ Re w ≤ 4
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). There is $A$ such that for every $\varepsilon > 0$ there is $C$ with the following property. Let $u$ be an $S$-integer (`SInt 𝔪`) that is not a sixth power in $F$, generating the extension to the $S$-integers of a nonzero ideal $\mathfrak u$ of $\mathcal O_F$, and let $\mathfrak b \ne 0$ be an ideal contained in every prime containing $\mathfrak u$. Then there is an entire function $\Lambda$ equal to `kummerL ι 𝔪 u w` $= L^S(w, \chi_\bullet(u))$ for $\operatorname{Re} w > 1$ and satisfying $|\Lambda(w)| \le C\,\mathrm N\mathfrak b^{1/2+\varepsilon}(1 + |\operatorname{Im} w|)^A$ for $0 \le \operatorname{Re} w \le 4$.
--
--   This extends (8.14), which the paper states for the frequency elements $u$ of the rows, to every $u$ that is not a sixth power, with the bound in terms of any $\mathfrak b$ divisible by the radical of $\mathfrak u$, on the wider strip $0 \le \operatorname{Re} w \le 4$. It is the convexity input to `exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le` (Lemma 8.1 on the rows), whose off-diagonal terms are the series $L^S(w, \chi_\bullet(u_r^5 u_{r'}))$ for two distinct rows. Like (8.14), it rests on Lemma 3.3 (the Kummer characters $\chi_\bullet(u)$ and their conductors) and the convexity bound (8.3). The constants may depend on $\mathfrak m$, $g$ and $\varepsilon$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 56: “The numerator for each of these rows is entire. From Equation (8.3) and the omitted-factor bound, $L^S(w, \chi_\bullet(u)) \ll_\epsilon U^{1/2+\epsilon}(2 + |\operatorname{Im} w|)^{A_F}$ $(.003 \le \operatorname{Re} w \le 4)$. (8.14)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 56, (8.14), extended to every u that is not a sixth power (the convexity input to Lemma 8.1 on the rows; Lemma 3.3 and (8.3))

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le_of_ne_pow_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∃ A : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ (u : SInt 𝔪) (𝔲 𝔟 : Ideal (𝓞 F)), 𝔲 ≠ ⊥ →
          Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) → (∀ b : F, b ^ 6 ≠ (u : F)) →
          𝔟 ≠ ⊥ → (∀ P : Ideal (𝓞 F), P.IsPrime → 𝔲 ≤ P → 𝔟 ≤ P) →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 u w) ∧
            ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 4 →
              ‖Λ w‖ ≤ C * (Ideal.absNorm 𝔟 : ℝ) ^ (1 / 2 + ε) * (1 + |w.im|) ^ A := by
  sorry

end ArtinPrimitiveRoots
