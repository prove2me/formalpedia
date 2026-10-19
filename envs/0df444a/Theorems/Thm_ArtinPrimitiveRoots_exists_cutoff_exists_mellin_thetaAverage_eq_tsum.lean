-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_mellin_thetaAverage_eq_tsum
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-18T04:51:28.653526+00:00
-- url     : https://prove2.me/theorems/2b898c8c-29ef-4331-a77e-adf890a5ed78
-- title:
--   Lemma 6.3 of OpenAI's Primitive roots paper before the radial smoothing — the theta average T_m(l) in forward form equals its reflected expansion
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. For a prime of norm $q$ and $e \ge 0$ let $\beta(q, e)$ be $1$ if $e = 0$, $q^{-k}$ if $e = 3k + 1$, $q^{1/2-k}$ if $e = 3k$ with $k \ge 1$, and $0$ otherwise (the $\beta_{\mathfrak p}(e)$ of (6.20)). There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`).
--
--   There are a measurable $V : \mathbb R \to \mathbb R$, an integer $r \ge 0$ and constants $C_0, A_0 > 0$ such that, for every complex $s$ with $\operatorname{Re} s > -5/6$, the Mellin transform of $V$ converges at $s$ (`MellinConvergent`) and
--   $$\widehat V(s) = C_0 A_0^s\,\big(\Gamma(s + 5/6)\Gamma(s + 7/6)\big)^r.$$
--   There are also a finite type $T$, complex functions $\omega, \rho, \lambda$ and $H$ of $(\upsilon, \mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n', s)$ with $\upsilon \in U_S/U_S^6$ (`SClass 𝔪`), ideals $\mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n'$ and $s \in T$ ($\rho$ and $\lambda$ taking a further ideal, $H$ a further real number), and $\alpha > 0$, such that:
--   - $|\omega| \le \prod_{\mathfrak p \mid \mathfrak f}\beta(q_{\mathfrak p}, v_{\mathfrak p}(\mathfrak a'))$, and $\omega = 0$ unless every prime factor of $\mathfrak a'$ divides $\mathfrak f$;
--   - $|\rho| \le 1$ and $|\lambda| \le 1$;
--   - $t \mapsto H(e^t)$ is $C^2$, and for every $N > 0$ there is $C$ with $|(d/dt)^jH(e^t)| \le C\min(e^{\alpha t}, e^{-Nt})$ for $j \le 2$, all $t$ and all indices;
--   - for every row class $r = (\mathfrak b, \upsilon)$ (`RowClass 𝔪`, with $m$ = `rowElt g r`), every $\mathfrak h$ with $\mathfrak h\,\mathfrak d = \mathfrak b$, where $\mathfrak d$ = `simplePart 𝔟` is the product of the primes dividing $\mathfrak b$ exactly once, and every $l > 0$,
--   $$\sum_{\mathfrak c, \mathfrak n}\frac{\gamma_2(\mathfrak c)}{q_{\mathfrak c}^{1/2}q_{\mathfrak n}}\,\vartheta(\mathfrak A)\,\chi_{\mathfrak A}(m)\,V(q_{\mathfrak A}l) = \sum_{\mathfrak f, \mathfrak a', \mathfrak n', s} \frac{\omega}{q_{\mathfrak n'}}\,\rho(\mathfrak d)\sum_{\mathfrak c'} \frac{\lambda(\mathfrak c')\,\chi_{\mathfrak d}(c')^3}{q_{\mathfrak c'}^{1/2}}\,H\Big(\frac{q_{\mathfrak a'} q_{\mathfrak c'} q_{\mathfrak n'}^3}{l\,q_{\mathfrak d}^2 q_{\mathfrak f}^2}\Big),$$
--   with $\omega, \rho, \lambda, H$ evaluated at $(\upsilon, \mathfrak h, \mathfrak f, \mathfrak a', \mathfrak n', s)$, as `tsum`s. On the left $\mathfrak c$ runs over the squarefree exterior ideals, $\mathfrak n$ over the exterior ideals, $\mathfrak A = \mathfrak c\mathfrak n^3$, $\gamma_2(\mathfrak c)$ = `gaussPhase g 2 𝔠`, $\vartheta(\mathfrak A)$ = `χ.thetaChar g 𝔄` and $\chi_{\mathfrak A}(m)$ = `residueSymbol ι 𝔪 𝔄 m` (bundle `Def_ArtinHeckeTheta`). On the right $\mathfrak f$ runs over the squarefree ideals with $\mathfrak f^2 \mid \mathfrak h$, $\mathfrak a'$ over the nonzero ideals, $\mathfrak n'$ and $\mathfrak c'$ over the exterior ideals, $\mathfrak c'$ squarefree, $c'$ = `g.gen 𝔠'` and $\chi_{\mathfrak d}(c')$ = `residueSymbol ι 𝔪 𝔡 c'`.
--
--   In the paper $V$ is the radial profile (5.20), whose Mellin transform is (5.21), with $r$ the number of complex places. The left side is the quotient average $\mathcal T_m(l)$ in its forward form, (6.10) of Lemma 6.1, written with the factors of the theta sum (4.2) (`χ.thetaSum`, with $P_G(q_{\mathfrak A}/Z)$ replaced by $V(q_{\mathfrak A}l)$). The right side is the same average in its reflected form, the minus average of (6.9) as evaluated in the proof of Lemma 6.3 through (6.32), before the $T$-average. Its profiles are $H = \sum_{\ell} H_{\upsilon,\kappa_6(\mathfrak t;s_d,s_c),\ell}$ of (6.21); the coefficients and index ranges are those of Lemma 6.3 and (6.24)–(6.26), as in `exists_cutoff_exists_thetaSum_rowElt_eq_tsum`. The bounds on $H$ are the ones that statement asserts for $\Phi$, (6.22) for $j \le 2$ in the variable $t = \log x$; Lemma 5.5 states that the $\Phi$ inherit them from the profiles $H_\kappa$ of Theorem 5.4.
--
--   It is a cut for `exists_cutoff_exists_thetaSum_rowElt_eq_tsum` (Lemma 6.3 and (6.22)): the reduction proves the rest of Lemma 5.5 (the kernel $\mathcal K$, (5.22) and (5.23)), the forward average (6.11) and the reflected $T$-average in Lean.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 26: “**Lemma 5.5** (Exact Gaussian smoothing). For $V$ in (5.20), there are constants $C_0 > 0$ and $A_0 > 0$ such that $\widehat V(s) = C_0A_0^s\big[\Gamma(s + 5/6)\Gamma(s + 7/6)\big]^r$ $(\operatorname{Re} s > -5/6)$. (5.21)”; p. 30: “We may now define the quotient average $\mathcal T_m(l) = \int_{X_l/\Gamma}\mathbf 1_B([y])L(y)^{-1}\mathscr D_m^+(y)\,\mathrm d_l^\times y = \int_{X_l/\Gamma}\mathbf 1_B([y])L(y)^{-1}\mathscr D_m^-(y)\,\mathrm d_l^\times y.$ (6.9) **Lemma 6.1** (Theta representation of the smoothed sum). Let $V$ and $\mathcal K$ be the common unrotated profile and Gaussian averaging weight from Theorem 5.5. For $l, Z > 0$, $\mathcal T_m(l) = \sum_{\mathfrak c\ \text{squarefree},\ \mathfrak n}\frac{\gamma_2(\mathfrak c)}{q_{\mathfrak c}^{1/2}q_{\mathfrak n}}L(A)\prod_{\mathfrak p\mid\mathfrak m}\chi_{\mathfrak p}(A)^{j_{\mathfrak p}}V(q_{\mathfrak A}l)$, (6.10) $B_m(Z) = \int_0^\infty\mathcal K(T)\mathcal T_m(T/Z)\frac{\mathrm dT}{T}$. (6.11) Here $\mathfrak A = \mathfrak c\mathfrak n^3$ and $A = cn^3$ is an allowed product generator. The ideal sums are over integral exterior ideals.”; p. 33, (6.21): “$H_{\upsilon,\kappa,\ell}(x) = \int_{X_x}\mathbf 1_B(\kappa[v]^{-1})H_S(\kappa, [v])^2L_\upsilon(v)\times\prod_{a\in S}f_{\upsilon,\ell,a}(v_a)\,\mathrm d_x^\times v$, $\Phi_{\upsilon,\kappa,\ell}(x) = \int_0^\infty\mathcal K(T)H_{\upsilon,\kappa,\ell}(x/T)\frac{\mathrm dT}{T}$, $\Phi_{\upsilon,\kappa}(x) = \sum_{\ell=1}^{J_\upsilon}\Phi_{\upsilon,\kappa,\ell}(x)$.”; p. 37: “The sheet norm is $\frac{|\nu_0|_S}{l} = \frac{q_{\mathfrak a'_{\mathfrak f}}q_{\mathfrak c'}q_{\mathfrak n'}^3}{q_{\mathfrak d}^2q_{\mathfrak f}^2l}$; there is no norm Jacobian. […] Insert the two class partitions, use Equation (6.31), and split the fixed $S$-function into its $\ell$-terms. Putting $l = T/Z$ in Equation (6.11) produces precisely the combined profile in Equation (6.21), and hence Equation (6.27).”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 27–37, proof of Lemma 6.3, before the radial smoothing of Lemma 5.5 (the forward theta average T_m(l) of Lemma 6.1 against the weight V of (5.21) equals its reflected expansion, by Proposition 5.1, Corollary 5.2, Lemmas 5.3–5.4 and 6.2)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_exists_mellin_thetaAverage_eq_tsum (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  let βp : ℝ → ℕ → ℝ := fun q e =>
    if e = 0 then 1
    else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
    else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
    else 0
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
        ∏ P ∈ (normalizedFactors 𝔣).toFinset,
          βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ l : ℝ, 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  sorry

end ArtinPrimitiveRoots
