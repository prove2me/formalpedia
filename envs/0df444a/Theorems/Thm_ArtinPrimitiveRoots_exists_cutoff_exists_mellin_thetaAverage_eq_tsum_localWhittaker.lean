-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-18T07:02:40.09109+00:00
-- url     : https://prove2.me/theorems/93d56f1c-364e-434d-875d-cb17efe6009b
-- title:
--   Lemma 6.3 of OpenAI's Primitive roots paper, the theta identity unfolded — the forward theta average T_m(l) equals its reflected Fourier expansion with explicit exterior Whittaker data
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`); $R$ is the ring of $S$-integers (`SInt 𝔪`), $U_S$ its units, and $p$ = `g.gen P` the allowed generator of an exterior prime $P$.
--
--   The local data at an exterior prime $P$ of norm $q$ are written with these symbols (all `let`s of the statement):
--   - $\chi_P(t)$ for $t \in F$: $\chi_P(y)\overline{\chi_P(z)}$ for a representation $zt = y$ with $y, z \in R$, $z \notin PR$, and $0$ if there is none, where $\chi_P$ on $R$ is `sexticResidueSymbol ι 𝔪 P`; and $\psi_P(w/p) = e(-y/p)$ for $y \in R$ with $y \equiv w \pmod P$ (`sAddChar`);
--   - $W_P(e) = q^{-k}$ if $e = 3k$, $q^{-k-1/2}\gamma_2(P)$ if $e = 3k+1$, $0$ if $e \equiv 2 \pmod 3$, with $\gamma_2(P)$ = `gaussPhase g 2 P`, and $W_P(a(p^{e}t)) = \chi_P(t)^{2e}W_P(e)$ for $e \ge 0$, $0$ for $e < 0$;
--   - the masks $\alpha_{P,j}$ on $R/PR$: for $j \ne 0$, $\tau_{P,j}^{-1}\overline{\chi_P(v)}^{\,j}$ with $\tau_{P,j} = \sum_v \overline{\chi_P(v)}^{\,j}\psi_P(v/p)$; for $j = 0$, $1 - q^{-1}$ at $v = 0$ and $-q^{-1}$ otherwise;
--   - for a digit $v \ne 0$ and $e = e_0 + 2 \ge 0$, the value $W_P(e)\,\chi_P(t)^{4+2e}\chi_P(v)^4\,\psi_P(p^{e-1}t/v)$ (and $0$ for $e < 0$);
--   - $E_P(e_0, t) = W_P(a(p^{e_0}t))$ if $P \nmid \mathfrak b$, and otherwise the masked digit sum $\sum_v \alpha_{P,j}(v)\,(\cdots)$ with $j = v_P(\mathfrak b) \bmod 6$, the zero digit contributing $W_P(a(p^{e_0}t))$ and a digit $v \ne 0$ the value above.
--
--   There are a measurable $V$, $r \ge 0$ and $C_0, A_0 > 0$ with $\widehat V(s) = C_0A_0^s(\Gamma(s+5/6)\Gamma(s+7/6))^r$ for $\operatorname{Re} s > -5/6$ (as in `exists_cutoff_exists_mellin_thetaAverage_eq_tsum`), a finite group $\mathcal V$, a map $[\,\cdot\,] : F \to \mathcal V$ multiplicative on $F^\times$ and trivial on $U_S^6$, functions $L_\upsilon : F \to \mathbb C$ ($\upsilon \in U_S/U_S^6$) multiplicative and of absolute value $1$ on $F^\times$ and equal to $1$ on $U_S$, profiles $H_{\upsilon,\kappa}$ ($\kappa \in \mathcal V$) with $t \mapsto H_{\upsilon,\kappa}(e^t)$ of class $C^2$ and, for every $N > 0$, $|(d/dt)^jH_{\upsilon,\kappa}(e^t)| \le C_N\min(e^{\alpha t}, e^{-Nt})$ for $j \le 2$, uniformly, and $\alpha > 0$, such that for every row class $r = (\mathfrak b, \upsilon)$ with $m$ = `rowElt g r`, $b$ = `g.gen 𝔟`, and every $l > 0$,
--   $$\sum_{\mathfrak c, \mathfrak n}\frac{\gamma_2(\mathfrak c)}{q_{\mathfrak c}^{1/2}q_{\mathfrak n}}\,\vartheta(\mathfrak A)\,\chi_{\mathfrak A}(m)\,V(q_{\mathfrak A}l) = \sum_{x}\Big(\prod_{P \mid \mathfrak x\mathfrak b}E_P\big(v_P(\nu),\,\nu p^{-v_P(\nu)}\big)\Big)\,L_\upsilon(\nu)^{-1}\,H_{\upsilon,[\nu]}\Big(\frac{q_{\mathfrak x}}{q_{\mathfrak b}^2\,l}\Big),\qquad \nu = x/b^2,$$
--   as `tsum`s. The left side is that of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum`. On the right $x = (\mathfrak x, \varepsilon)$ runs over `RowClass 𝔪`, i.e. $x$ = `rowElt g` $(\mathfrak x, \varepsilon)$ runs over $(R \setminus 0)/U_S^6$, and $v_P(\nu) = v_P(\mathfrak x) - 2v_P(\mathfrak b)$.
--
--   In the paper this is the identity of the two expressions of the quotient average (6.9), each Fourier-expanded and unfolded. The forward form is (6.10) of Lemma 6.1. The reflected form uses the exterior Whittaker values (5.6) of Proposition 5.1, the masks (6.3), the per-digit Weyl values in the proof of Lemma 6.2, and the $S$-unfolding (6.32). The reflected frequencies $\nu \in F^\times/\Gamma$ with a nonzero exterior coefficient have $\nu b^2 \in R$, so they are written as $x/b^2$. $L_\upsilon$ is $L_S\lambda_{\varepsilon_m}$ of (6.2); $\mathcal V = F_S^\times/F_S^{\times6}$; and $H_{\upsilon,\kappa}$ is the profile of (6.21) before the radial average, summed over $\ell$. The statement packages Proposition 5.1 (Kazhdan–Patterson), Lemmas 5.3–5.4, the lift identity (5.4) behind Lemma 6.2, and the two orbit unfoldings. Lemma 6.2's digit sums, the factor separation (6.29)–(6.31) and the bounds of Lemma 6.3 are not part of it. Together with `exists_cutoff_digitSum_eq_mul_localSymbol_pow`, it gives `exists_cutoff_exists_mellin_thetaAverage_eq_tsum`, and that reduction is proved in Lean.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 32: “The effective torus law gives, for integers $e_1, e_2$ and units $u, v$, $\mathcal C_{\mathfrak p}(p^{e_1}u, p^{e_2}v) = \chi_{\mathfrak p}(u)^{2e_2}\chi_{\mathfrak p}(v)^{-2e_1}$. The unit–unit and uniformizer–uniformizer factors are trivial. Thus torus multiplication contributes $\mathcal C_{\mathfrak p}(p^{e-2}t, p^2v^{-2}) = \chi_{\mathfrak p}(t)^4\chi_{\mathfrak p}(v)^{4(e-2)}$. The remaining spherical argument is $p^etv^{-2}$. It is zero for $e < 0$; otherwise Equation (5.6) contributes $\chi_{\mathfrak p}(t)^{2e}\chi_{\mathfrak p}(v)^{-4e}W_e$.”; p. 36: “The reflected $S$-factor is $\mathcal C_S(\gamma\nu_0, y^{-1})f_{w,\upsilon}(\gamma\nu_0/y)$. In the legitimate substitution $v = \gamma\nu_0/y$, $[y] = [\nu_0][v]^{-1}$ and $L(y)^{-1} = L(\nu_0)^{-1}L(v)$. […] We obtain the exact identity $\sum_{\gamma\in\Gamma}\int_{\Omega_l}\mathbf 1_B([y])L(y)^{-1}\mathcal C_S(\gamma\nu_0, y^{-1})f_{w,\upsilon}(\gamma\nu_0/y)\,\mathrm d_l^\times y = L(\nu_0)^{-1}\int_{X_{|\nu_0|_S/l}}\mathbf 1_B([\nu_0][v]^{-1})H_S(\nu_0, v)^2L(v)f_{w,\upsilon}(v)\,\mathrm d^\times_{|\nu_0|_S/l}v$. (6.32)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 18–19, 28–36, the identity (6.9) of the two theta averages T_m(l), Fourier-expanded and unfolded: the forward form (6.10) equals the sum over the reflected frequencies of the exterior Whittaker values (5.6), the masks (6.3) and the per-digit Weyl values of the proof of Lemma 6.2, against the S-unfolded profiles (6.32) (Proposition 5.1, Lemmas 5.3–5.4 and the unfoldings)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (𝒱 : Type) (_ : CommGroup 𝒱) (_ : Fintype 𝒱) (cls : F → 𝒱) (L : SClass 𝔪 → F → ℂ)
      (H : SClass 𝔪 → 𝒱 → ℝ → ℂ) (α : ℝ), 0 < α ∧
      (∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b) ∧
      (∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1) ∧
      (∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b) ∧
      (∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1) ∧
      (∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1) ∧
      (∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' z : RowClass 𝔪,
            (∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
              Eloc P ((normalizedFactors r.1.1).count P)
                (((normalizedFactors z.1.1).count P : ℤ) -
                  2 * ((normalizedFactors r.1.1).count P : ℤ))
                ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2 *
                  (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
                    2 * ((normalizedFactors r.1.1).count P : ℤ))))) *
            (L r.2 ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))⁻¹ *
            H r.2 (cls ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))
              ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) := by
  sorry

end ArtinPrimitiveRoots
