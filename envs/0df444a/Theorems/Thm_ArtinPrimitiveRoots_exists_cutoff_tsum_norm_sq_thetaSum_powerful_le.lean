-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_powerful_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_powerful_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T22:29:57.002859+00:00
-- url     : https://prove2.me/theorems/8b8d61e8-9ecf-44f1-916d-b156baf95da8
-- title:
--   Proof of Proposition 4.1 of OpenAI's Primitive roots paper, (6.40)–(6.45) — the reflected second moment of B_m(Z) for one powerful part 𝔥 and one row-unit class
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For all real $c_2$ and $\varepsilon > 0$ there is $C$ such that for all real $Z \ge 2$, $P, D \ge 1$, every class $\upsilon \in U_S/U_S^6$ (`SClass 𝔪`) and every ideal $\mathfrak h$ with $P \le q_{\mathfrak h} < 2P$,
--   $$\sum_{r} |B_{m_r}(Z)|^2 \le C\,Z^{\varepsilon}\Big(D + \frac{D^2P}{Z}\Big),$$
--   as a `HasSum`, where $r = (\mathfrak b, \upsilon)$ runs over the row classes (`RowClass 𝔪`) with unit class $\upsilon$ and $\mathfrak b = \mathfrak h\,\mathfrak d$ for $\mathfrak d$ = `simplePart 𝔟` (the product of the primes dividing $\mathfrak b$ exactly once, so $\mathfrak h$ is the powerful part of $\mathfrak b$), with $q_{\mathfrak b} \le c_2 Z^{M_0}$, $M_0 = 1033/1000$, and $D \le q_{\mathfrak d} < 2D$. Here $q$ is the absolute norm, $m_r$ = `rowElt g r` and $B_m(Z)$ = `χ.thetaSum g m Z` (bundle `Def_ArtinHeckeTheta`). The constant may depend on $\mathfrak m$, $\chi$, $g$, $c_2$ and $\varepsilon$, not on $Z, P, D, \upsilon, \mathfrak h$.
--
--   This is the bound the proof of Proposition 4.1 obtains for one powerful part before summing over $\mathfrak h$: the discarded terms (6.40)–(6.42) and the retained terms (6.43)–(6.45) for fixed $\mathfrak h$ and row-unit class, combined with the losses of p. 41. Summing it over the $O(P^{1/2})$ powerful ideals of (6.39) and the finitely many classes $\upsilon$ gives (4.5), `exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le`. It follows from Lemma 6.3 (`exists_cutoff_exists_thetaSum_rowElt_eq_tsum`) and Lemma 6.4 (`exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le`).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 40: “Sum these norms over the admitted $\mathfrak f$ and the finite $s$, using Equation (6.41) for the former. Square the resulting estimate for each fixed $\mathfrak h$, and only then sum the squares over $\mathfrak h$. Since each row has a unique powerful part, no triangle inequality across different powerful parts is necessary.” and p. 39: “The initial element-to-ideal reduction lets us fix one row-unit class $\upsilon \in U_6$ and sum over ideal rows at a bounded cost.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 39–41, proof of Proposition 4.1, the reflected second moment for one powerful part 𝔥 and one row-unit class, before the sum over 𝔥 by (6.39)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_thetaSum_powerful_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₂ ε : ℝ), 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z → ∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
          ∀ (υ : SClass 𝔪) (𝔥 : Ideal (𝓞 F)), P ≤ (Ideal.absNorm 𝔥 : ℝ) →
            (Ideal.absNorm 𝔥 : ℝ) < 2 * P →
            ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 // r.2 = υ ∧
                𝔥 * simplePart r.1.1 = r.1.1 ∧
                (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
                D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
                (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                  ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
              σ ≤ C * Z ^ ε * (D + D ^ 2 * P / Z) := by
  sorry

end ArtinPrimitiveRoots
