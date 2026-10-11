-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_freqSeries_principalFreq_eq
-- name    : ArtinPrimitiveRoots.exists_cutoff_freqSeries_principalFreq_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T14:05:26.689501+00:00
-- url     : https://prove2.me/theorems/7932aa2c-7ac0-4ecf-8a5f-6fbbd4bba0af
-- title:
--   Proposition 7.3 (7.12) of OpenAI's Primitive roots paper, at u = 1 — the principal frequency series is ζ^S(6z)ζ^S(w)·ℋ₁(ξ, w, z)/L(ξ, χ), with ℋ₁ an explicit Euler product
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`), and all complex $\xi, w, z$ with $\operatorname{Re}\xi > 3$, $\operatorname{Re} w > 3$, $\operatorname{Re} z > 1$:
--   $$F_1(\xi, w, z) = \frac{\zeta^S(6z)\,\zeta^S(w)\,\mathcal H_1(\xi, w, z)}{L(\xi, \chi)}.$$
--   Here $F_1$ is the frequency series (7.11) at the principal frequency (`χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z`, bundle `Def_ArtinHeckeTheta`). $\zeta^S(s) = \prod_{P \mid \mathfrak m}(1 - NP^{-s})\,\zeta_F(s)$, with $\zeta_F$ Mathlib's Dedekind zeta function and the product over the nonzero primes containing $\mathfrak m$. $L(\xi, \chi)$ is `χ.LSeries ξ`. $\mathcal H_1$ is the product (`tprod`) over the nonzero primes $P$ coprime to $\mathfrak m$ of
--   $$\frac{1}{1 - D}\Bigl[(1 - W) + W(1 - V) + \frac{E\bigl((1 - Q^{-1})(1 - W) + W(1 - V)(1 - W)\bigr) - D\bigl((1 - V)(1 - W) + (Q - 1)WV(1 - W)\bigr)}{1 - E}\Bigr],$$
--   with $Q = NP$, $V = Q^{-6z}$, $W = Q^{-w}$, $D = \chi(P)Q^{-\xi}$ and $E = \overline{\texttt{jacobiPhaseSix}\ \iota\ P}\cdot\chi(P)^6Q^{4-6\xi}V$ (bundle `Def_ArtinHeckeProbe`): the paper's local factor (7.17)–(7.19) at $u = 1$, multiplied out.
--
--   At $u = 1$ the paper's $L^S(w, \chi_\bullet(1))$ is $\zeta^S(w)$ and $L^S(\xi, \eta\chi_\bullet(1))$ is $L^S(\xi, \eta)$. The statement takes the half-planes $\operatorname{Re}\xi > 3$, $\operatorname{Re} w > 3$, $\operatorname{Re} z > 1$, inside the paper's region of absolute convergence; holomorphy and bounds of $\mathcal H_1$ in the paper's larger regions are a separate matter. It is a cut for `exists_cutoff_norm_rowIntegral_principalFreq_sub_le` ((8.12)–(8.13)).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 46: “Proposition 7.3. For every $u \in U$, the series in Equation (7.11) has the Euler factorization $F_u(\xi, w, z) = \frac{\zeta_F^S(6z)L^S(w, \chi_\bullet(u))}{L^S(\xi, \eta\chi_\bullet(u))}H_u(\xi, w, z)$ (7.12) initially in absolute convergence.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 46–48, Proposition 7.3, (7.12) at u = 1, with the local factor (7.17)–(7.19)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_freqSeries_principalFreq_eq (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ξ w z : ℂ), 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z =
          (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-(6 * z)))) * dedekindZeta F (6 * z) *
            ((∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-w))) * dedekindZeta F w) *
            (∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
              let Q : ℕ := Ideal.absNorm P.1
              let V := (Q : ℂ) ^ (-(6 * z))
              let W := (Q : ℂ) ^ (-w)
              let D := χ.toFun P.1 * (Q : ℂ) ^ (-ξ)
              let E := starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6 *
                (Q : ℂ) ^ (4 - 6 * ξ) * V
              ((1 - W) + W * (1 - V) + (E * ((1 - (Q : ℂ)⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
                D * ((1 - V) * (1 - W) + ((Q : ℂ) - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)) /
            χ.LSeries ξ := by
  sorry

end ArtinPrimitiveRoots
