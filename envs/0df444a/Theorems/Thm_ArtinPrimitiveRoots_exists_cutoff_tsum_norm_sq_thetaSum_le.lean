-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T13:00:17.733052+00:00
-- url     : https://prove2.me/theorems/bcd08bd8-7482-41cc-ac36-89df9800747c
-- title:
--   Proposition 4.1 of OpenAI's Primitive roots paper — the reflected second moment of the theta sums B_m(Z)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. Put $M_0 = 1033/1000$. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`), and all real $c_1 > 0$, $c_2$ and $\varepsilon > 0$. There is $C$ such that for every real $Z \ge 2$, writing $B_m(Z) = $ `χ.thetaSum g m Z` and summing over the row classes $r = (\mathfrak b, \cdot)$ (`RowClass 𝔪`) with $c_1Z^{M_0} \le \mathrm N\mathfrak b \le c_2Z^{M_0}$, of row $m = $ `rowElt g r`:
--
--   1. for all real $P, D \ge 1$, the sum of $|B_m(Z)|^2$ over those classes with $P \le \mathrm N\mathfrak b/\mathrm N\mathfrak d < 2P$ and $D \le \mathrm N\mathfrak d < 2D$, where $\mathfrak d = $ `simplePart 𝔟` is the product of the primes dividing $\mathfrak b$ exactly once, converges to a value at most $C Z^{\varepsilon}P^{1/2}(D + D^2P/Z)$;
--   2. the sum of $|B_m(Z)|^2$ over all those classes converges to a value at most $C Z^{2M_0 - 1 + \varepsilon}$.
--
--   Here $\mathfrak b = (m)R$ and $\mathrm N\mathfrak b = q_m$; $\mathfrak d = \mathfrak d(m)$ and $\mathfrak b/\mathfrak d = \mathfrak h(m)$ in the paper's notation (p. 16). The paper sums over the elements $m$ of a box $R \cap \ell_{Z^{M_0}}\mathscr K$ for a compact $\mathscr K \subset F_S^\times$; here the sum runs over the classes $mU_S^6$, on which $B_m(Z)$ is constant, with $q_m/Z^{M_0}$ in a compact subinterval of $(0, \infty)$. Each such class has a balanced representative in one such box (Lemma 3.2), so the sums here are bounded by the paper's. The constant $C$ may depend on $\mathfrak m$, $\chi$, $g$, $c_1$, $c_2$ and $\varepsilon$, as the paper's depends on $F$, $S$, $\eta$, $\mathscr K$ and $\epsilon$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 17, Proposition 4.1: “Let $F$ be a fixed cyclotomic field containing $\mu_{12}$, let $S$ and the arithmetic data be as above, and fix a compact subset $\mathscr K \subset F_S^\times$. For every $\epsilon > 0$, every $Z \ge 2$, and all dyadic lengths $P, D \ge 1$, $\sum_{m \in \mathscr B_Z(\mathscr K),\ P \le q_{\mathfrak h(m)} < 2P,\ D \le q_{\mathfrak d(m)} < 2D}|B_m(Z)|^2 \ll_{F,S,\eta,\mathscr K,\epsilon} Z^\epsilon P^{1/2}\bigl(D + \frac{D^2P}{Z}\bigr)$. (4.5) In particular, $\sum_{m \in \mathscr B_Z(\mathscr K)}|B_m(Z)|^2 \ll_{F,S,\eta,\mathscr K,\epsilon} Z^{2M_0-1+\epsilon}$. (4.6)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 17, Proposition 4.1, (4.5)–(4.6)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_thetaSum_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
          (∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
            ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
                c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
                (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
                P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
                (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
                D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
                (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                  ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
              σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z)) ∧
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000)} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + ε) := by
  sorry

end ArtinPrimitiveRoots
