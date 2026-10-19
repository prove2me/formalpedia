-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul
-- name    : ArtinPrimitiveRoots.exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:39:35.729438+00:00
-- url     : https://prove2.me/theorems/0d3d9816-b2aa-47cd-b5de-c3760eba380a
-- title:
--   Proposition 7.3 (7.14)–(7.18) of OpenAI's Primitive roots paper, for every u — the row coefficients are normalized, multiplicative prime by prime, with local tables
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`) and every frequency class $r$ (`FreqClass 𝔪`). Put $u$ = `freqElt g r`, let $\mathfrak u = r.1$ be its exterior ideal, and
--   $$a(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r) = \gamma_2(\mathfrak c)\,\vartheta(\mathfrak c\mathfrak n^3)\,F\bigl(\mathfrak s, \mathfrak c\mathfrak n^3, u\cdot g(\mathfrak r)^6\bigr),$$
--   with $\gamma_2$ = `gaussPhase g 2`, $\vartheta$ = `χ.thetaChar g` and $F$ = `poissonFactor g` (bundle `Def_ArtinHeckeTheta`). Write $\theta_P = \chi_P(u)$ = `residueSymbol ι 𝔪 P u` and $Q = NP$. Then:
--   1. $a(1, 1, 1, 1) = 1$;
--   2. for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`), all $e_0 \le 1$ and $l, k, m \ge 0$, and all ideals $\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r$ coprime to $\mathfrak m$ and not divisible by $P$, with $\mathfrak c$ squarefree:
--   $$a(P^{e_0}\mathfrak c, P^l\mathfrak n, P^k\mathfrak s, P^m\mathfrak r) = a(P^{e_0}, P^l, P^k, P^m)\,a(\mathfrak c, \mathfrak n, \mathfrak s, \mathfrak r);$$
--   3. at such a prime with $P \nmid \mathfrak u$: $\theta_P^6 = 1$, and for $e_0 \le 1$
--   $$a(P^{e_0}, P^l, P^k, P^m) = \theta_P^{\,k}\,\overline{\theta_P}^{\,e_0+3l}\,c_P(e_0, l, k, m),$$
--   where $c_P$ = `principalLocalCoeff` $(Q, \chi(P), \overline{\texttt{jacobiPhaseSix}\ \iota\ P}\,\chi(P)^6)$ (bundles `Def_ArtinHeckeLocalCoeff` and `Def_ArtinHeckeProbe`) is the table at $u = 1$;
--   4. at such a prime with $P \mid \mathfrak u$: $\theta_P = 0$; $a(1, 1, P^k, P^m) = 1$ if $k = 0$ and $0$ otherwise; $a(P^{e_0}, P^l, P^k, P^m) = 0$ for $k \ge 2$; and for $e_0 \le 1$
--   $$|a(P^{e_0}, P^l, P^k, P^m)| \le Q^{e_0+3l}\,\sqrt Q^{\,k}.$$
--
--   These are the coefficient facts behind the Euler factorization (7.12) for a general row $u$: the cross-prime cancellation and the factorization $\mathcal F_u = \prod_P \mathcal F_{u,P}$ of (7.16); the unit multiplier (7.14), which at $P \nmid u$ is $\theta_P^{k-t}$ with $t = e_0 + 3l$, against the table at $u = 1$ (the factor $\theta_P^{-3l}$ is $1$ wherever that table is nonzero, since there $l$ is even, so the statement writes it as $\overline{\theta_P}^{\,t}$); and at $P \mid u$ the values $C_{0,k}(J) = 1_{J=0}$, $C_{t,k}(J) = 0$ for $k \ge 2$, and the bounds (7.18). The statement is the arithmetic half of `exists_cutoff_exists_freqSeries_mul_twistedL_eq` (Proposition 7.3, (7.12)–(7.13) for $u \ne 1$), which follows from it by the analytic estimates (7.19)–(7.22) of the local factors. Its counterpart at the principal frequency is `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul`. The multiplicativity and the twisted tables were checked numerically in $\mathbb Q(\zeta_{12})$ (four values of $u$, primes of norms 13, 37 and 61, including primes dividing $u$).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 47–48: “The unit multiplier removed by these changes is exactly $\chi_p(h_p)^{k-t}\chi_p(s_p)^t\chi_p(A_p)^{t-k}$. (7.14) […] Thus all cross-prime terms cancel […] For $t = 0$ the value is $C_{0,0}(J) = 1$, and $C_{0,k}(J) = 1_{J=0}$ for $k > 0$. […] $C_{t,k}(J) = 0$ ($k \ge 2$). (7.17) […] In particular, for $t > 0$, $|C_{t,0}(J)| \le Q^t$, $|C_{t,1}(J)| \le Q^{t+1/2}$, (7.18) with the support restrictions visible in Equation (7.17).”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46–48, proof of Proposition 7.3, (7.14)–(7.18) for every u (normalization, prime-by-prime multiplicativity and the local tables of the row coefficients)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g r * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * a 𝔠 𝔫 𝔰 𝔯) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ¬ r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) ^ 6 = 1 ∧
          ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
              residueSymbol ι 𝔪 P (freqElt g r) ^ k *
                starRingEnd ℂ (residueSymbol ι 𝔪 P (freqElt g r)) ^ (e₀ + 3 * l) *
                principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) = 0 ∧
          (∀ k m : ℕ, a (P ^ 0) (P ^ 0) (P ^ k) (P ^ m) = if k = 0 then 1 else 0) ∧
          (∀ e₀ l k m : ℕ, 2 ≤ k → a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) = 0) ∧
          (∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            ‖a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m)‖ ≤
              (Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k)) := by
  sorry

end ArtinPrimitiveRoots
