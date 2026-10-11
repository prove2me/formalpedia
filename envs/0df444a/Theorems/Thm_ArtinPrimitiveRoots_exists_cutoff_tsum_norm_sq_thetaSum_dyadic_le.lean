-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T22:29:21.257894+00:00
-- url     : https://prove2.me/theorems/74cd1058-f389-46aa-82aa-3849470c461a
-- title:
--   Proposition 4.1, (4.5), of OpenAI's Primitive roots paper — the reflected second moment of the theta sums B_m(Z) on one dyad of powerful and squarefree parts
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For all real $c_1 > 0$, $c_2$ and $\varepsilon > 0$ there is $C$ such that for all real $Z \ge 2$ and $P, D \ge 1$
--   $$\sum_{r} |B_{m_r}(Z)|^2 \le C\,Z^{\varepsilon} P^{1/2}\Big(D + \frac{D^2P}{Z}\Big),$$
--   as a `HasSum`, where $r = (\mathfrak b, \upsilon)$ runs over the row classes (`RowClass 𝔪`, the nonzero $S$-integers modulo $U_S^6$) with $c_1Z^{M_0} \le q_{\mathfrak b} \le c_2 Z^{M_0}$, $M_0 = 1033/1000$, $P \le q_{\mathfrak b}/q_{\mathfrak d} < 2P$ and $D \le q_{\mathfrak d} < 2D$. Here $q$ is the absolute norm, $\mathfrak d$ = `simplePart 𝔟` is the product of the primes dividing $\mathfrak b$ exactly once (so $q_{\mathfrak b}/q_{\mathfrak d} = q_{\mathfrak h}$ for the powerful part $\mathfrak h$), $m_r$ = `rowElt g r` and $B_m(Z)$ = `χ.thetaSum g m Z` (bundle `Def_ArtinHeckeTheta`).
--
--   This is the first conjunct of `exists_cutoff_tsum_norm_sq_thetaSum_le` (Proposition 4.1), from which the second, (4.6), follows by summing over the $O((\log Z)^2)$ dyads (the last paragraph of the proof, p. 41). The sum over the box $B_Z(\mathcal K)$ is replaced by the sum over row classes, as in that statement: $B_m$ is constant on classes, and $P, D$ may be any reals $\ge 1$. The constant may depend on $\mathfrak m$, $\chi$, $g$, $c_1$, $c_2$ and $\varepsilon$, as the paper's depends on $F, S, \eta, \mathcal K, \epsilon$. It follows from Lemma 6.3 (`exists_cutoff_exists_thetaSum_rowElt_eq_tsum`) and Lemma 6.4 (`exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le`) by the argument of pp. 39–41.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 17: “**Proposition 4.1** (Reflected second moment). Let $F$ be a fixed cyclotomic field containing $\mu_{12}$, let $S$ and the arithmetic data be as above, and fix a compact subset $\mathcal K \subset F_S^\times$. For every $\epsilon > 0$, every $Z \ge 2$, and all dyadic lengths $P, D \ge 1$, $\sum_{m \in B_Z(\mathcal K),\ P \le q_{\mathfrak h(m)} < 2P,\ D \le q_{\mathfrak d(m)} < 2D}|B_m(Z)|^2 \ll_{F,S,\eta,\mathcal K,\epsilon} Z^{\epsilon}P^{1/2}\big(D + \frac{D^2P}{Z}\big)$. (4.5)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 17, 39–41, Proposition 4.1, (4.5) (the reflected second moment on the dyads P ≤ q_𝔥 < 2P, D ≤ q_𝔡 < 2D)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z → ∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
              P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
              (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) := by
  sorry

end ArtinPrimitiveRoots
