-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_freqSeries_mul_twistedL_eq
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_freqSeries_mul_twistedL_eq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T20:45:16.559338+00:00
-- url     : https://prove2.me/theorems/2f05c984-2ca3-48af-a243-56d34516ee5e
-- title:
--   Proposition 7.3 (7.12)–(7.13) of OpenAI's Primitive roots paper, u ≠ 1 — the Euler factorization of the row series, with correction holomorphic and O(q_u^ε) on the first region
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). For every $\varepsilon > 0$ there is $C$ such that for every frequency class $r \ne$ `principalFreq 𝔪` (`FreqClass 𝔪`), with $u$ = `freqElt g r` and $q_u$ the norm of $r.1$, there is a function $\mathcal H$ of $(\xi, w, z)$ which is holomorphic (`DifferentiableOn ℂ` as a function on $\mathbb C^3$) on `regionOne`, satisfies $|\mathcal H| \le C q_u^{\varepsilon}$ there, and for $\operatorname{Re}\xi > 3$, $\operatorname{Re} w > 3$, $\operatorname{Re} z > 1$
--   $$\mathcal F_u(\xi, w, z)\cdot L^S(\xi, \eta\overline{\chi_\bullet(u)}) = \zeta_F^S(6z)\,L^S(w, \chi_\bullet(u))\,\mathcal H(\xi, w, z),$$
--   with $\mathcal F_u$ = `χ.freqSeries g u` (bundle `Def_ArtinHeckeTheta`) and `twistedL`, `zetaSF`, `kummerL`, `regionOne` from `Def_ArtinHeckeRowL`.
--
--   This is Proposition 7.3 for $u \ne 1$ on the first region of (7.13), enlarged by $10^{-5}$ as in its proof (p. 49), with (7.12) multiplied by the denominator; the initial region contains the lines of (7.10). The second region and the statements about $\mathcal H_1$ are not part of it. The constant may depend on $\mathfrak m$, $\chi$, $g$ and $\varepsilon$, as the paper's depends on $F, S, \eta, \epsilon$.
--
--   The Euler structure behind (7.12) for general $u$, the prime-by-prime multiplicativity (7.14)–(7.16) of the coefficients of $\mathcal F_u$, was checked numerically in $\mathbb Q(\zeta_{12})$ with the bundle objects evaluated literally: four values of $u$ (an S-unit outside $U_S^6$, and elements with exterior valuations 1, 2 and 5), at primes of norms 13, 37 and 61 including the primes dividing $u$, 9 runs of 4032 cases, no failure; breaking the reciprocity of one generator produces failures. The same check confirms the conjugate in the denominator: the coefficient at $(\mathfrak p, 1, 1, 1)$ carries $\overline{\chi_{\mathfrak p}(u)}$, and the one at $(1, 1, \mathfrak p, 1)$ carries $\chi_{\mathfrak p}(u)$. The analytic bounds (7.20)–(7.22) for the local corrections were not checked.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 46: “**Proposition 7.3.** For every $u \in \mathcal U$, the series in Equation (7.11) has the Euler factorization $\mathcal F_u(\xi, w, z) = \frac{\zeta_F^S(6z)L^S(w,\chi_\bullet(u))}{L^S(\xi,\eta\overline{\chi_\bullet(u)})}\mathcal H_u(\xi, w, z)$ (7.12) initially in absolute convergence. The correction $\mathcal H_u$ is holomorphic in open neighborhoods of both real-part regions $\operatorname{Re}\xi \ge .998, \operatorname{Re} w \ge .003, \operatorname{Re} z \ge .4,\ \operatorname{Re}\xi \ge .998, \operatorname{Re} w \ge .95, \operatorname{Re} z \ge .16.$ (7.13) For every $\epsilon > 0$ it satisfies $|\mathcal H_u(\xi, w, z)| \ll_{F,S,\eta,\epsilon} q_u^{\epsilon}$ there, uniformly in all heights.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46–50, Proposition 7.3, (7.12)–(7.13), for u ≠ 1 on the first region

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_freqSeries_mul_twistedL_eq (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ C : ℝ,
        ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ H : ℂ → ℂ → ℂ → ℂ,
          DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) regionOne ∧
          (∀ p ∈ regionOne, ‖H p.1 p.2.1 p.2.2‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ ε) ∧
          ∀ ξ w z : ℂ, 3 < ξ.re → 3 < w.re → 1 < z.re →
            χ.freqSeries g (freqElt g r) ξ w z * twistedL ι χ (freqElt g r) ξ =
              zetaSF 𝔪 (6 * z) * kummerL ι 𝔪 (freqElt g r) w * H ξ w z := by
  sorry

end ArtinPrimitiveRoots
