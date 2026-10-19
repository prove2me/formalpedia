-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:22:50.442982+00:00
-- url     : https://prove2.me/theorems/bb3ab5b4-3938-405e-bb13-88e70bb78426
-- title:
--   (8.3) of OpenAI's Primitive roots paper for the rows — outside finitely many u, L^S(ξ, η conj χ•(u)) is entire and O(q_u^{1/2+ε}(2 + |Im ξ|)^A) on .003 ≤ Re ξ ≤ 4
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\eta$ of modulus $\mathfrak m$ (`χ : HeckeChar F 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). There are a finite set $P$ of frequency classes (`FreqClass 𝔪`) and $A$ such that for every $\varepsilon > 0$ there is $C$ with the following property: for every frequency class $r \ne$ `principalFreq 𝔪` with $r \notin P$, with $u$ = `freqElt g r` and $q_u$ the norm of $r.1$, there is an entire function $\Lambda$ equal to `twistedL ι χ u ξ` $= L^S(\xi, \eta\overline{\chi_\bullet(u)})$ for $\operatorname{Re} \xi > 1$ and satisfying $|\Lambda(\xi)| \le C q_u^{1/2+\varepsilon}(2 + |\operatorname{Im} \xi|)^A$ for $.003 \le \operatorname{Re} \xi \le 4$.
--
--   This is the convexity bound (8.3) applied to the primitive character $\omega_u$ inducing $\eta\overline{\chi_\bullet(u)}$ (p. 51), together with the omitted-factor bound that follows it, which passes from $L_F(\xi, \omega_u)$ to the $S$-incomplete series $L^S$. The paper states (8.3) for nonprincipal $\omega$ only; the finite set $P$ is where the rows with principal $\omega_u$ go. The paper's $N\mathfrak f_\omega \ll U$ on the dyad $U \le q_u < 2U$ becomes the factor $q_u^{1/2+\varepsilon}$, and the exponent $A$ is the paper's $A_F$. The constants may depend on $\mathfrak m$, $\eta$, $g$ and $\varepsilon$. It is the analogue for the twisted rows of `exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le` ((8.14)).
--
--   It is a cut for `exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one` (Proposition 8.2), together with `exists_cutoff_sum_norm_sq_sum_mul_conj_residueSymbol_le` (Lemma 8.1 for the rows).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 52: “We use standard Hecke continuation and the functional equation in a deliberately conservative convexity bound. For a nonprincipal primitive finite-order $\omega$ with $\mathrm N\mathfrak f_\omega \ll U$, there is an $A_F > 0$, depending on the fixed field, such that on any of the fixed strips below, in particular for $.003 \le \sigma \le 4$, $|L_F(\sigma + it, \omega)| \ll_{F,S,\eta,\epsilon} U^{1/2+\epsilon}(2 + |t|)^{A_F}$. (8.3)” and p. 52: “Omitting factors at a fixed set or at primes dividing $u$ changes a positive-real-part estimate by $q_u^\epsilon$”.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 52–53, (8.3) for the rows L^S(ξ, η conj χ•(u)) (the convexity bound, with the omitted-factor bound)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ P : Finset (FreqClass 𝔪), ∃ A : ℝ,
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → r ∉ P →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) ∧
            ∀ ξ : ℂ, 3 / 1000 ≤ ξ.re → ξ.re ≤ 4 →
              ‖Λ ξ‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |ξ.im|) ^ A := by
  sorry

end ArtinPrimitiveRoots
