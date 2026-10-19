-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T20:46:16.661627+00:00
-- url     : https://prove2.me/theorems/dbe1ee75-4c8d-4838-8f74-871ecdb9a3ab
-- title:
--   Proposition 8.2 (8.4) of OpenAI's Primitive roots paper — exceptional rows |E(U)| ≪ U^{1/2}; otherwise 1/L^S(ξ, η conj χ•(u)) ≪ U^ε on Re ξ ≥ .998, |Im ξ| ≤ 2U^ρ
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). There are $\rho > 0$, $C_0$, $U_0$ and finite sets $E(U)$ of frequency classes (`FreqClass 𝔪`) with $|E(U)| \le C_0 U^{1/2}$ for $U \ge U_0$, such that for every $\varepsilon > 0$ there is $C$ with the following property. For every $U \ge U_0$ and every frequency class $r \ne$ `principalFreq 𝔪` with $U \le q_u < 2U$ ($q_u$ the norm of $r.1$) and $r \notin E(U)$, with $u$ = `freqElt g r`, there is a function $D$ holomorphic on $\{\operatorname{Re}\xi > .997, |\operatorname{Im}\xi| < 3U^\rho\}$ with $D(\xi)\cdot$`twistedL ι χ u ξ` $= 1$ for $\operatorname{Re}\xi > 1$, $|\operatorname{Im}\xi| < 3U^\rho$, and $|D(\xi)| \le C U^{\varepsilon}$ for $\operatorname{Re}\xi \ge .998$, $|\operatorname{Im}\xi| \le 2U^\rho$.
--
--   This is Proposition 8.2 with (8.4): $D$ is the continuation of $L^S(\xi, \eta\overline{\chi_\bullet(u)})^{-1}$. Holomorphy on the slightly larger open region follows from the zero-free rectangle $\operatorname{Re} s \ge .996$, $|\operatorname{Im} s| \le 4U^\rho$ that defines $E(U)$, and from the exclusion of principal $\omega_u$. The membership condition of $E(U)$ in the dyad is not part of the statement. The constants may depend on $\mathfrak m$, $\chi$, $g$ and $\varepsilon$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 53: “**Proposition 8.2.** For the fixed $F, S, \eta$ there are $\rho > 0$ and $U_0$ with the following property. For every $U \ge U_0$, there is a set $\mathcal E(U) \subset \{u \in \mathcal U : U \le q_u < 2U\}$ of cardinality $|\mathcal E(U)| \ll_{F,S,\eta} U^{1/2}$ which contains every row for which $\omega_u$ is principal or $L_F(s, \omega_u)$ has a zero with $\operatorname{Re} s \ge .996$ and $|\operatorname{Im} s| \le 4U^\rho$. For $u \notin \mathcal E(U)$ and every $\epsilon > 0$, $|L^S(\xi, \eta\overline{\chi_\bullet(u)})^{-1}| \ll_{F,S,\eta,\epsilon} U^\epsilon$ $(\operatorname{Re}\xi \ge .998, |\operatorname{Im}\xi| \le 2U^\rho)$. (8.4)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 53–55, Proposition 8.2, (8.4)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_card_le_and_exists_mul_twistedL_eq_one (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ U₀ : ℝ,
        ∃ E : ℝ → Finset (FreqClass 𝔪),
          (∀ U : ℝ, U₀ ≤ U → ((E U).card : ℝ) ≤ C₀ * U ^ (1 / 2 : ℝ)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ r : FreqClass 𝔪,
            r ≠ principalFreq 𝔪 → U ≤ (Ideal.absNorm r.1.1 : ℝ) →
            (Ideal.absNorm r.1.1 : ℝ) < 2 * U → r ∉ E U →
            ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {ξ | 997 / 1000 < ξ.re ∧ |ξ.im| < 3 * U ^ ρ} ∧
              (∀ ξ : ℂ, 1 < ξ.re → |ξ.im| < 3 * U ^ ρ →
                D ξ * twistedL ι χ (freqElt g r) ξ = 1) ∧
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → ‖D ξ‖ ≤ C * U ^ ε := by
  sorry

end ArtinPrimitiveRoots
