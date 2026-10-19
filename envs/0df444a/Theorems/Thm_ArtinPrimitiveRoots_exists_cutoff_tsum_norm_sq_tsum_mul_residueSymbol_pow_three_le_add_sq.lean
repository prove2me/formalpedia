-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_sq
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_sq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-18T04:34:42.690004+00:00
-- url     : https://prove2.me/theorems/a7e19a77-94f3-4ddb-b2e2-013e0c3f76b6
-- title:
--   Goldmakher–Louvel's initial bound (E₂) for the exterior quadratic symbols χ_𝔡(c)³ of OpenAI's Primitive roots paper
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For every $\varepsilon > 0$ there is $K$ such that for all real $C, D \ge 1$ and every complex function $z$ on the squarefree exterior ideals $\mathfrak c$ of norm $q_{\mathfrak c} \le C$,
--   $$\sum_{\substack{\mathfrak d\ \text{squarefree exterior}\\ q_{\mathfrak d} \le D}} \Big|\sum_{\mathfrak c} z_{\mathfrak c}\,\chi_{\mathfrak d}(c)^3\Big|^2 \le K\,(D + C^2)\,(CD)^{\varepsilon} \sum_{\mathfrak c} |z_{\mathfrak c}|^2,$$
--   where $c$ = `g.gen 𝔠` and $\chi_{\mathfrak d}(c)$ = `residueSymbol ι 𝔪 𝔡 c` (bundle `Def_ArtinHeckeTheta`). The sums are `tsum`s over finite sets.
--
--   This is the bound (E₂) of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, Lemma 4.2, https://doi.org/10.1017/S0305004112000370, for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. Here the rows $\mathfrak d$ are Goldmakher–Louvel's $M$ and the columns $\mathfrak c$ their $N$. It is weaker than `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le` (Lemma 6.4), since $D + C^2 \ge C + D$ once $C \ge 1$. Together with `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent` (their Theorem 4.3), it is a cut for that lemma, through the iteration of their Theorem 4.1.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, Lemma 4.2 (the initial bound (E₂); for the family of Lemma 6.4 of OpenAI, Primitive roots for every admissible integer base, p. 38)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_sq (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (D + C ^ 2) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
