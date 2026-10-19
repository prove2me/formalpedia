-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:22:40.007981+00:00
-- url     : https://prove2.me/theorems/ad4ea5b9-a4f5-469a-ae04-87cff52f08f4
-- title:
--   Lemma 8.1 of OpenAI's Primitive roots paper for the rows — the conductor large sieve Σ_u |Σ b_𝔞 η(𝔞) conj χ_𝔞(u)|² ≪ (N + U²)(NU)^ε Σ |b_𝔞|² over q_u < 2U
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\eta$ of modulus $\mathfrak m$ (`χ : HeckeChar F 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For every $\varepsilon > 0$ there is $C$ such that for all real $U, N \ge 2$, every finite set $T$ of frequency classes $r$ (`FreqClass 𝔪`) with $q_u < 2U$ ($q_u$ the norm of $r.1$), every finite set $B$ of exterior ideals $\mathfrak a$ (`IsExterior 𝔪 𝔞`) of norm at most $N$ and every complex function $b$ on ideals,
--   $$\sum_{r \in T} \Big|\sum_{\mathfrak a \in B} b_{\mathfrak a}\,\eta(\mathfrak a)\,\overline{\chi_{\mathfrak a}(u)}\Big|^2 \le C\,(N + U^2)\,(NU)^{\varepsilon} \sum_{\mathfrak a \in B} |b_{\mathfrak a}|^2,$$
--   where $u$ = `freqElt g r` and $\chi_{\mathfrak a}(u)$ = `residueSymbol ι 𝔪 𝔞 u` (bundle `Def_ArtinHeckeTheta`).
--
--   This is Lemma 8.1, (8.2), for the family $\mathscr X(U)$ of the characters $\omega_u$ inducing $\eta\overline{\chi_\bullet(u)}$ (p. 51), written through the row coefficients $\eta(\mathfrak a)\overline{\chi_{\mathfrak a}(u)}$ on exterior ideals, the coefficients of `twistedL ι χ u`. The paper's family is the rows of one dyad $U \le q_u < 2U$; here $T$ is any finite set of rows with $q_u < 2U$, and the coefficients are supported on exterior ideals. The constant may depend on $\mathfrak m$, $\eta$, $g$ and $\varepsilon$, as the paper's depends on $F, S, C_0, \mathscr L_S, \epsilon$.
--
--   It is a cut for `exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one` (Proposition 8.2), together with `exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le` ((8.3) for the rows).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 51: “**Lemma 8.1** (Primitive conductor large sieve). Fix $C_0 > 0$ and a finite set $\mathscr L_S$ of possible local components at $S$. Let $\mathscr X(U)$ be any family of distinct primitive finite-order Hecke characters of $F$ whose conductor norms are at most $C_0U$ and whose components at $S$ belong to that set. For $N, U \ge 2$, any complex coefficients $b_{\mathfrak n}$, and every $\epsilon > 0$, $\sum_{\omega\in\mathscr X(U)}\big|\sum_{q_{\mathfrak n}\le N} b_{\mathfrak n}\omega(\mathfrak n)\big|^2 \ll_{F,S,C_0,\mathscr L_S,\epsilon} (N + U^2)(NU)^\epsilon \sum_{q_{\mathfrak n}\le N}|b_{\mathfrak n}|^2$. (8.2)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 51–52, Lemma 8.1, (8.2), for the family of rows ω_u of (8.1)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
        ∀ U N : ℝ, 2 ≤ U → 2 ≤ N → ∀ T : Finset (FreqClass 𝔪),
          (∀ r ∈ T, (Ideal.absNorm r.1.1 : ℝ) < 2 * U) → ∀ B : Finset (Ideal (𝓞 F)),
          (∀ I ∈ B, IsExterior 𝔪 I ∧ (Ideal.absNorm I : ℝ) ≤ N) → ∀ b : Ideal (𝓞 F) → ℂ,
            ∑ r ∈ T, ‖∑ I ∈ B, b I * (χ.toFun I *
                starRingEnd ℂ (residueSymbol ι 𝔪 I (freqElt g r)))‖ ^ 2 ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots
