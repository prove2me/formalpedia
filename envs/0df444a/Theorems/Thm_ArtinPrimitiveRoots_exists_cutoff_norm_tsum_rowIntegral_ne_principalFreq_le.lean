-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T12:58:31.137449+00:00
-- url     : https://prove2.me/theorems/acc3edd1-44a5-4128-ae13-9d93e806d407
-- title:
--   (8.21) of OpenAI's Primitive roots paper — the nonprincipal rows of the probe total O(Z^{7/15 − .0004})
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`), every smooth real $W_1$ with compact support in $(0, \infty)$ (`IsProbeWeight W₁`) and every $M$ holomorphic on $\operatorname{Re} z > 0$ with rapid vertical decay on its strips (`IsMellinWeight M`). There are $C$ and $Z_0$ such that for every real $Z \ge Z_0$ the sum (`tsum`) over the frequency classes $r \ne $ `principalFreq 𝔪` of the rows `χ.rowIntegral g W₁ M r` $(Z^{9/10}, Z^{133/1000}, Z)$ has modulus at most $C Z^{7/15 - 1/2500}$.
--
--   The rows are the terms $u \ne 1$ of (7.10) at the scales $X = Z^a$, $Y = Z^b$ of (4.4). The paper groups them into dyads $U \le q_u < 2U$ and bounds the sum of the dyadic totals $\mathcal J^{\mathrm{np}}_{2^j}(Z)$ by $Z^{C_*(1) - .0004}$, $C_*(1) = 7/15$; the sum over all rows $u \ne 1$ converges absolutely (p. 56), so it is the sum of the dyadic totals. The constants may depend on $\mathfrak m$, $\chi$, $g$, $W_1$ and $M$, as the paper's depend on $F$, $S$, $\eta$ and the weights.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 56: “It remains to bound the rows with $u \ne 1$. Split their sum on the initial lines into dyads $U \le q_u < 2U$, $U = 1, 2, 4, \dots$, before shifting any of them. Each dyad contains finitely many rows; the full sum on the initial lines is absolutely convergent.” and p. 58: “We have therefore proved $\sum_{j \ge 0}\mathcal J^{\mathrm{np}}_{2^j}(Z) \ll Z^{C_*(1)-.0004}$. (8.21)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 56, 58, (8.21) (the nonprincipal rows)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖∑' r : {r : FreqClass 𝔪 // r ≠ principalFreq 𝔪},
                χ.rowIntegral g W₁ M r.1 (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2500) := by
  sorry

end ArtinPrimitiveRoots
