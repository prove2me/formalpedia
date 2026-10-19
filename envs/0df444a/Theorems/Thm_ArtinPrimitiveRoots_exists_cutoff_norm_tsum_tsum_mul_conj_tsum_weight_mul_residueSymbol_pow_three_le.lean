-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:41:18.66417+00:00
-- url     : https://prove2.me/theorems/85b89dd7-9a97-4658-b24d-9526bb7e4e0e
-- title:
--   Goldmakher–Louvel's bound for the weighted gcd-sorted sums Σ₃ of the exterior quadratic symbols χ_𝔞(b)³ of OpenAI's Primitive roots paper
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every system of allowed generators $g$ (`AllowedGen ι 𝔪`) and every real $\alpha \ge 1$. Write $\chi_{\mathfrak b}(\mathfrak a)$ for `residueSymbol ι 𝔪 𝔞 (g.gen 𝔟) ^ 3` (bundle `Def_ArtinHeckeTheta`) and $q_{\mathfrak a}$ for the absolute norm. Suppose the hypothesis $(E_\alpha)$ of `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent`, stated there verbatim. Then there exist a function $W : \mathbb R \to \mathbb R$ with $0 \le W \le 1$, $W = 1$ on $(1, 2]$ and $W = 0$ on $[3, \infty)$, a natural number $k$ and a map `cls` from the ideals of $\mathcal O_F$ to `Fin k` such that for every $\varepsilon > 0$ there is $K$ with the following. For all real $M, N \ge 1$ and $L$ with
--   $$\frac{N^2}{M}(MN)^{\varepsilon} \le L \le \frac{M}{(MN)^{\varepsilon}},$$
--   every ideal $\mathfrak g$, every class $j$ and every complex function $z$ on the squarefree exterior ideals $\mathfrak b$ with $N < q_{\mathfrak b} \le 2N$ and `cls 𝔟 = j`,
--   $$\Big|\sum_{\substack{\mathfrak b_1, \mathfrak b_2\\ \mathfrak b_1 + \mathfrak b_2 = \mathfrak g}} z_{\mathfrak b_1}\overline{z_{\mathfrak b_2}} \sum_{\mathfrak a} W\Big(\frac{q_{\mathfrak a}}{M}\Big)\chi_{\mathfrak b_1}(\mathfrak a)\overline{\chi_{\mathfrak b_2}(\mathfrak a)}\Big| \le K q_{\mathfrak g}^{4} (MN)^{\varepsilon}\Big(M + N + \sqrt M L^{\alpha - 1/2} + \sqrt{M/L}\, N\Big)\sum_{\mathfrak b}|z_{\mathfrak b}|^2,$$
--   where $\mathfrak a$ runs over the exterior ideals with $L\, q_{\mathfrak b}^2 < q_{\mathfrak a}$ for every ideal $\mathfrak b$ with $\mathfrak b^2 \mid \mathfrak a$ (the squarefree part of $\mathfrak a$ has norm $> L$). The powers of $L$ are real powers.
--
--   This is Proposition 5.2 of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. The sum is their $\Sigma_3(M, N, L, \mathfrak g, j, z)$ with $[\mathfrak b_1] = [\mathfrak b_2] = j$; their smooth weight, class group and class map are the existential $W$, $k$ and `cls`. It is a cut for `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent` (their Theorem 4.3), through their Lemma 5.1, the iteration (5.3)–(5.4) and their Lemma 4.4.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, Proposition 5.2 (the bound for B₃; a cut for Theorem 4.3, for the family of Lemma 6.4 of OpenAI, Primitive roots for every admissible integer base, p. 38)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
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
        ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t ∧ W t ≤ 1) ∧ (∀ t, 1 < t → t ≤ 2 → W t = 1) ∧
          (∀ t, 3 ≤ t → W t = 0) ∧
          ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
            ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
              N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
              ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
                (z : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
                  N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j} → ℂ),
                ‖∑' 𝔟₁, ∑' 𝔟₂, if 𝔟₁.1 ⊔ 𝔟₂.1 = 𝔤 then
                    z 𝔟₁ * starRingEnd ℂ (z 𝔟₂) *
                      ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧
                          ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
                            L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
                        (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) *
                          residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₁.1) ^ 3 *
                          starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₂.1) ^ 3)
                  else 0‖ ≤
                  K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
                    (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
                    ∑' 𝔟, ‖z 𝔟‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
