-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_thetaSum_rowElt_eq_tsum
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_thetaSum_rowElt_eq_tsum
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T21:17:00.60938+00:00
-- url     : https://prove2.me/theorems/73498c04-c06a-4b39-af15-5e95aa2062af
-- title:
--   Lemma 6.3 and (6.22) of OpenAI's Primitive roots paper — the reflected expansion of the theta sum B_m(Z), with its coefficient and profile bounds
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. For a prime of norm $q$ and $e \ge 0$ let $\beta(q, e)$ be $1$ if $e = 0$, $q^{-k}$ if $e = 3k + 1$, $q^{1/2-k}$ if $e = 3k$ with $k \ge 1$, and $0$ otherwise (the $\beta_{\mathfrak p}(e)$ of (6.20)). There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`).
--
--   There are a finite type $T$, complex functions $\omega, \rho, \lambda$ and $\Phi$ of $(\upsilon, \mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n', s)$ with $\upsilon \in U_S/U_S^6$ (`SClass 𝔪`), ideals $\mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n'$ and $s \in T$ ($\rho$ and $\lambda$ taking a further ideal, $\Phi$ a further real number), and $\alpha > 0$, such that:
--   - $|\omega| \le \prod_{\mathfrak p \mid \mathfrak f}\beta(q_{\mathfrak p}, v_{\mathfrak p}(\mathfrak a'))$, and $\omega = 0$ unless every prime factor of $\mathfrak a'$ divides $\mathfrak f$;
--   - $|\rho| \le 1$ and $|\lambda| \le 1$;
--   - $t \mapsto \Phi(e^t)$ is $C^2$, and for every $N > 0$ there is $C$ with $|(d/dt)^j\Phi(e^t)| \le C\min(e^{\alpha t}, e^{-Nt})$ for $j \le 2$, all $t$ and all indices;
--   - for every row class $r = (\mathfrak b, \upsilon)$ (`RowClass 𝔪`, the nonzero elements of the $S$-integers modulo $U_S^6$, with $m$ = `rowElt g r`), every $\mathfrak h$ with $\mathfrak h\,\mathfrak d = \mathfrak b$, where $\mathfrak d$ = `simplePart 𝔟` is the product of the primes dividing $\mathfrak b$ exactly once, and every $Z > 0$,
--   $$B_m(Z) = \sum_{\mathfrak f, \mathfrak a', \mathfrak n', s} \frac{\omega}{q_{\mathfrak n'}}\,\rho(\mathfrak d)\sum_{\mathfrak c'} \frac{\lambda(\mathfrak c')\,\chi_{\mathfrak d}(c')^3}{q_{\mathfrak c'}^{1/2}}\,\Phi\Big(\frac{Z q_{\mathfrak a'} q_{\mathfrak c'} q_{\mathfrak n'}^3}{q_{\mathfrak d}^2 q_{\mathfrak f}^2}\Big),$$
--   with $\omega, \rho, \lambda, \Phi$ evaluated at $(\upsilon, \mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n', s)$, as `tsum`s. Here $\mathfrak f$ runs over the squarefree ideals with $\mathfrak f^2 \mid \mathfrak h$, $\mathfrak a'$ over the nonzero ideals, $\mathfrak n'$ and $\mathfrak c'$ over the exterior ideals, $\mathfrak c'$ squarefree, $c'$ = `g.gen 𝔠'`, $\chi_{\mathfrak d}(c')$ = `residueSymbol ι 𝔪 𝔡 c'` and $B_m(Z)$ = `χ.thetaSum g m Z` (bundle `Def_ArtinHeckeTheta`).
--
--   In the paper $s = (u, s_d, s_c)$ runs over $U_6 \times B^2$, $\omega = \omega_{\upsilon,\mathfrak t}$ (6.24), $\rho = \rho_{\upsilon,\mathfrak t,s_d}$ (6.25), $\lambda = \lambda_{\upsilon,\mathfrak t,s_c}$ (6.26) and $\Phi = \Phi_{\upsilon,\kappa_6(\mathfrak t;s_d,s_c)}$ (6.21) for the frozen tuple $\mathfrak t = (\mathfrak h, \mathfrak f, \mathfrak a'_{\mathfrak f}, \mathfrak n', u)$. The paper's ranges $\mathfrak f \in \mathcal F(\mathfrak h)$, $\mathfrak a' \in \mathcal A(\mathfrak f)$ and $(\mathfrak n', \mathfrak f) = 1$ lie inside the ranges above and are recovered by zero coefficients ($\beta$ vanishes off $\mathcal A(\mathfrak f)$). The bound (6.22) is used for $j \le 2$ in the variable $t = \log x$, where $(x\partial_x)^j$ becomes $(d/dt)^j$. The row-unit class is $\upsilon = r.2$: allowed generators are unique modulo $U_S^6$, so $m = \upsilon\cdot$`g.gen 𝔟` gives $\upsilon_m = \upsilon$.
--
--   The statement is not satisfiable degenerately: the identity determines $B_m(Z)$, and the bounds alone make its right side absolutely convergent, so no junk value of a `tsum` can occur. It is a cut for `exists_cutoff_tsum_norm_sq_thetaSum_le` (Proposition 4.1), together with `exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le` (Lemma 6.4); the paper's proof of Lemma 6.3 rests on Proposition 5.1 (the cubic theta representation), Corollary 5.2, Lemmas 5.3–5.5, 6.1 and 6.2.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 33: “The local bounds for the fixed rotated vectors and Theorems 5.4 and 5.5 therefore give one $\alpha > 0$ such that, for every $N > 0$ and integer $j \ge 0$, $|(x\partial_x)^j\Phi_{\upsilon,\kappa}(x)| \ll_{N,j} \min(x^{\alpha}, x^{-N})$ $(x > 0)$. (6.22) The constants are uniform in $\upsilon \in U_6$ and $\kappa \in \mathcal V$.”; p. 34: “**Lemma 6.3** (The reflected expansion). For every nonzero $m \in R$ and $Z > 0$, let $(m)_S = \mathfrak h\mathfrak d$ and $\upsilon = \upsilon_m$. Then $B_m(Z) = \sum_{\mathfrak f \in \mathcal F(\mathfrak h)}\sum_{\mathfrak a'_{\mathfrak f} \in \mathcal A(\mathfrak f),\ \mathfrak n',\ (\mathfrak n',\mathfrak f) = 1}\ \sum_{u \in U_6,\ s_d, s_c \in B}\frac{\omega_{\upsilon,\mathfrak t}}{q_{\mathfrak n'}}\ \rho_{\upsilon,\mathfrak t,s_d}(\mathfrak d)\Big[\sum_{\mathfrak c'\ \text{squarefree}}\frac{\lambda_{\upsilon,\mathfrak t,s_c}(\mathfrak c')}{q_{\mathfrak c'}^{1/2}}\chi_{\mathfrak d}(c')^3\ \Phi_{\upsilon,\kappa_6(\mathfrak t;s_d,s_c)}\Big(\frac{Zq_{\mathfrak a'_{\mathfrak f}}q_{\mathfrak c'}q_{\mathfrak n'}^3}{q_{\mathfrak d}^2q_{\mathfrak f}^2}\Big)\Big]$. (6.27) All ideal sums are over integral exterior ideals, and the expansion is absolutely convergent. The coefficients satisfy $|\omega_{\upsilon,\mathfrak t}| \le \beta_{\mathfrak f}(\mathfrak a'_{\mathfrak f})$, $|\rho_{\upsilon,\mathfrak t,s_d}| \le 1$, $|\lambda_{\upsilon,\mathfrak t,s_c}| \le 1$.” and p. 33, (6.20): “$\beta_{\mathfrak p}(e) = 1$ ($e = 0$), $q_{\mathfrak p}^{-k}$ ($e = 1 + 3k$, $k \ge 0$), $q_{\mathfrak p}^{1/2-k}$ ($e = 3k$, $k \ge 1$), $0$ otherwise; $\beta_{\mathfrak f}(\mathfrak a'_{\mathfrak f}) = \prod_{\mathfrak p\mid\mathfrak f}\beta_{\mathfrak p}(v_{\mathfrak p}(\mathfrak a'_{\mathfrak f}))$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 33–34, Lemma 6.3 and (6.22) (the reflected expansion of B_m(Z), with the bounds on its coefficients and profiles)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_exists_thetaSum_rowElt_eq_tsum (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      ∃ (T : Type) (_ : Fintype T)
        (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
        (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
        (α : ℝ), 0 < α ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
          ∏ P ∈ (normalizedFactors 𝔣).toFinset,
            βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
        (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
          ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
            C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
        (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
          ∀ Z : ℝ, 0 < Z →
          χ.thetaSum g (rowElt g r) Z =
            ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
                {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
              ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
                ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
                ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                  lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                    residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                    ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                    Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                      (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                          (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                        ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                          (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  sorry

end ArtinPrimitiveRoots
