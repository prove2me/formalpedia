-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T21:16:50.289137+00:00
-- url     : https://prove2.me/theorems/b6fc3e16-9562-47ce-b255-0c8150c8154e
-- title:
--   Lemma 6.4 of OpenAI's Primitive roots paper — the quadratic large sieve for the exterior symbols χ_𝔡(c)³ (Goldmakher–Louvel)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For every $\varepsilon > 0$ there is $K$ such that for all real $C, D \ge 1$ and every complex function $z$ on the squarefree exterior ideals $\mathfrak c$ (`IsExterior 𝔪 𝔠`, `Squarefree 𝔠`) of norm $q_{\mathfrak c} \le C$,
--   $$\sum_{\substack{\mathfrak d\ \text{squarefree exterior}\\ q_{\mathfrak d} \le D}} \Big|\sum_{\mathfrak c} z_{\mathfrak c}\,\chi_{\mathfrak d}(c)^3\Big|^2 \le K\,(C + D)\,(CD)^{\varepsilon} \sum_{\mathfrak c} |z_{\mathfrak c}|^2,$$
--   where $c$ = `g.gen 𝔠` is the allowed generator of $\mathfrak c$ and $\chi_{\mathfrak d}(c)$ = `residueSymbol ι 𝔪 𝔡 c` (bundle `Def_ArtinHeckeTheta`). The sums are `tsum`s over finite sets.
--
--   Since $\chi_{\mathfrak p}$ is a sextic residue symbol, $\chi_{\mathfrak d}(c)^3 = \prod_{\mathfrak p \mid \mathfrak d}(c/\mathfrak p)_2$ is the quadratic symbol, the value at $\mathfrak d$ of the quadratic Hecke character of $F(\sqrt c)/F$ (p. 38). The constant may depend on $\mathfrak m$, $g$ and $\varepsilon$, as the paper's depends on $F, S, \epsilon$.
--
--   This is the quadratic large sieve of Heath-Brown, in the number-field form of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, Theorem 1.1, https://doi.org/10.1017/S0305004112000370; it is reference [8] of the paper, which verifies Definition 1 of Goldmakher–Louvel for this family on pp. 38–39. It is a cut for `exists_cutoff_tsum_norm_sq_thetaSum_le` (Proposition 4.1), together with `exists_cutoff_exists_thetaSum_rowElt_eq_tsum` (Lemma 6.3).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38: “**Lemma 6.4** (Quadratic large sieve for the exterior symbols). For $C, D \ge 1$ and complex coefficients $z_{\mathfrak c}$ supported on squarefree exterior ideals with $q_{\mathfrak c} \le C$, one has, for every $\epsilon > 0$, $\sum_{\mathfrak d\ \text{squarefree},\ q_{\mathfrak d}\le D}\big|\sum_{\mathfrak c\ \text{squarefree},\ q_{\mathfrak c}\le C} z_{\mathfrak c}\chi_{\mathfrak d}(c)^3\big|^2 \ll_{F,S,\epsilon} (C + D)(CD)^{\epsilon}\sum_{\mathfrak c}|z_{\mathfrak c}|^2.$ (6.37)”
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, Theorem 1.1 (the quadratic large sieve over number fields; cited as [8] for Lemma 6.4, (6.37), of OpenAI, Primitive roots for every admissible integer base, p. 38)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (C + D) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
