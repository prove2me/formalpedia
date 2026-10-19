-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:34:46.302861+00:00
-- url     : https://prove2.me/theorems/10138558-0a49-4c21-953b-c3504776faed
-- title:
--   Goldmakher–Louvel's recursive estimate for the exterior quadratic symbols χ_𝔡(c)³ of OpenAI's Primitive roots paper
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every system of allowed generators $g$ (`AllowedGen ι 𝔪`) and every real $\alpha \ge 1$. Write $S(C, D, z)$ for
--   $$\sum_{\substack{\mathfrak d\ \text{squarefree exterior}\\ q_{\mathfrak d} \le D}} \Big|\sum_{\mathfrak c} z_{\mathfrak c}\,\chi_{\mathfrak d}(c)^3\Big|^2,$$
--   with $z$ a complex function on the squarefree exterior ideals $\mathfrak c$ of norm $q_{\mathfrak c} \le C$, $c$ = `g.gen 𝔠` and $\chi_{\mathfrak d}(c)$ = `residueSymbol ι 𝔪 𝔡 c` (bundle `Def_ArtinHeckeTheta`). Suppose that for every $\varepsilon > 0$ there is $K$ with $S(C, D, z) \le K (D + C^{\alpha}) (CD)^{\varepsilon} \sum |z_{\mathfrak c}|^2$ for all real $C, D \ge 1$ and all $z$. Then for every $\varepsilon > 0$ there is $K$ with
--   $$S(C, D, z) \le K\,\big(D + C + C^{2\alpha - 1} D^{1-\alpha}\big)\,(CD)^{\varepsilon} \sum_{\mathfrak c} |z_{\mathfrak c}|^2$$
--   for all real $C, D \ge 1$ and all $z$. The powers are real powers.
--
--   This is the recursive estimate of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, Theorem 4.3, https://doi.org/10.1017/S0305004112000370, for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. It is stated here with the rows cut off by $q_{\mathfrak d} \le D$ rather than dyadically; their Lemma 4.4 converts between the two. Its conclusion is weaker than `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le` (Lemma 6.4). Together with `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_sq` (their Lemma 4.2), it is a cut for that lemma, through the iteration of their Theorem 4.1.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, Theorem 4.3 (the recursive estimate; for the family of Lemma 6.4 of OpenAI, Primitive roots for every admissible integer base, p. 38)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2) →
        ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε *
                ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
