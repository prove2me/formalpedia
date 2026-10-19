-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
-- name    : ArtinPrimitiveRoots.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T10:52:44.673989+00:00
-- url     : https://prove2.me/theorems/e91f21f6-f87e-4037-a63d-6833cbecf337
-- title:
--   The Dedekind zeta input of Goldmakher–Louvel's Proposition 5.2 — (s − 1)ζ_F(s) is entire, polynomially bounded on Re s ≥ −1/2, with its Dirichlet series and Euler factors
-- statement:
--   Let $F$ be a number field. There is an entire function $R$ with:
--
--   1. $R(s) = (s - 1)\zeta_F(s)$ for $\operatorname{Re} s > 1$, where $\zeta_F$ is `dedekindZeta F`;
--   2. $R(1)$ = `dedekindZeta_residue F`, the residue of $\zeta_F$ at $s = 1$;
--   3. for every real $X$ there are $C, A \ge 0$ with $|R(s)| \le C(1 + |\operatorname{Im} s|)^A$ for $-1/2 \le \operatorname{Re} s \le X$.
--
--   In addition, for $\operatorname{Re} s > 1$, $\zeta_F(s) = \sum_I q_I^{-s}$ over all ideals $I$ of $\mathcal O_F$, where $q_I$ is the absolute norm (and $0^{-s} = 0$). For real $\sigma > 1$ the series $\sum_I q_I^{-\sigma}$ converges. Finally, let $g$ be a complex function on the ideals with $g(IJ) = g(I)g(J)$ for all $I, J$ and $\sum_I g(I)$ summable, and let $T$ be a finite set of nonzero prime ideals. Then
--   $$\Big(\sum_I g(I)\Big)\prod_{P \in T}\big(1 - g(P)\big) = \sum_{I:\ I \not\subseteq P \text{ for all } P \in T} g(I).$$
--
--   These are the facts about $\zeta_k$ that L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, take as standard in §3. The last identity, with $g(I) = q_I^{-s}$ or a twist of it, gives the Dirichlet series over the ideals coprime to a fixed ideal. They are used in the explicit formula for $\Sigma_3$ in their §6, here for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38.
--
--   It is a cut for `exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le` (their Proposition 5.2), together with `exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation`.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, §3 (the Dedekind zeta function: continuation of (s − 1)ζ_k with polynomial bounds, its Dirichlet series and Euler factors at finitely many primes; a cut for Proposition 5.2)

import Mathlib

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
    (F : Type*) [Field F] [NumberField F] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta F s) ∧
      R 1 = (dedekindZeta_residue F : ℂ) ∧
      (∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ A) ∧
      (∀ s : ℂ, 1 < s.re → dedekindZeta F s = ∑' I : Ideal (𝓞 F), (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      (∀ σ : ℝ, 1 < σ → Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) ∧
      (∀ g : Ideal (𝓞 F) → ℂ, (∀ I J, g (I * J) = g I * g J) → Summable g →
        ∀ T : Finset (Ideal (𝓞 F)), (∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) →
          (∑' I, g I) * ∏ P ∈ T, (1 - g P) =
            ∑' I, ({I | ∀ P ∈ T, ¬ I ≤ P} : Set (Ideal (𝓞 F))).indicator g I) := by
  sorry

end ArtinPrimitiveRoots
