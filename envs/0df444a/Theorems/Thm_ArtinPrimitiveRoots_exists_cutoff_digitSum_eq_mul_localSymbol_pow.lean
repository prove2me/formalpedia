-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_digitSum_eq_mul_localSymbol_pow
-- name    : ArtinPrimitiveRoots.exists_cutoff_digitSum_eq_mul_localSymbol_pow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:12:06.740999+00:00
-- url     : https://prove2.me/theorems/0433f3ce-e03c-4b7e-a1e0-b40e97380259
-- title:
--   Lemma 6.2 of OpenAI's Primitive roots paper — the masked digit sums of the local Weyl calculation are monomials in the local sextic symbol, with their bounds
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every system of allowed generators $g$ (`AllowedGen ι 𝔪`) and every exterior prime $P$ of norm $q$, with $p$ = `g.gen P`, $R$ = `SInt 𝔪`, $v$ the $P$-adic valuation and $\chi_P$ = `sexticResidueSymbol ι 𝔪 P` on $R$.
--
--   The local symbols $\chi_P(t)$ ($t \in F$), $\psi_P(w/p)$, the values $W_P(e)$ and $W_P(a(p^{e_0}t))$, the masks $\alpha_{P,j}$, the per-digit Weyl values and the factor $E_P$ are the `let`s of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`. Put $\mathcal R_{P,j,e_0}(t) = \sum_{v \ne 0}\alpha_{P,j}(v)\,W_e\,\chi_P(t)^{4+2e}\chi_P(v)^4\psi_P(p^{e-1}t/v)$ with $e = e_0 + 2$ (and $0$ if $e < 0$). This is the right side of (6.14), and the left side is $\mathcal R_{\mathfrak p,j,e}(t)$ of Lemma 6.2. Then:
--   - $\chi_P$ is multiplicative on $R$ with $\chi_P(x)^6 = 1$ for $x \notin PR$; $x \notin PR$ if and only if $v(x) = 1$; and the valuation of $\mathrm{gen}\,I$ is $v_P(I)$, written `WithZero.exp (-v_P(I))`, for every exterior $I$;
--   - on $t \in F$ with $v(t) = 1$, $\chi_P$ is multiplicative, satisfies $\chi_P(t)^6 = 1$, and agrees with $\chi_P$ on $R \setminus PR$;
--   - for $k \ne 0$, $E_P$ with $j = k \bmod 6$ equals $\alpha_{P,j}(0)\,W_P(a(p^{e_0}t)) + \mathcal R_{P,j,e_0}(t)$, and $\alpha_{P,j}(0) = 0$ for $j \ne 0$;
--   - (6.16): for $j < 6$, $e_0 + 2 \ge 0$ and $v(t) = 1$, $\mathcal R_{P,j,e_0}(t) = \mathcal R_{P,j,e_0}(1)\,\chi_P(t)^{b}$ with $b = 8 + 5j$ if $e = 0$ and $b = 4 + 2e$ if $e > 0$;
--   - (6.15): $\mathcal R_{P,1,e_0}(t) = 0$ when $e > 0$ and $v(t) \le 1$;
--   - $|\mathcal R_{P,j,e_0}(1)| \le \beta_P(e)$, the majorant of (6.20); $|\alpha_{P,j}(0)| \le 1$; and $|\gamma_2(P)| \le 1$.
--
--   The exponent $8 + 5j$ is the paper's $b_{j,0} \equiv 8 - j \pmod 6$. The statement starts from the per-digit values that the proof of Lemma 6.2 derives from the lift identity (5.4) and the cocycle; those values are part of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`, and this statement holds the finite-field part of the lemma. It is used, with that cut, for `exists_cutoff_exists_mellin_thetaAverage_eq_tsum`, and it supplies the local facts used in the proof of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker` from its three cuts.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 31: “**Lemma 6.2** (Local effect of reflection). Let $\mathfrak p$ be an exterior prime and put $W_e = W_{\mathfrak p}(a(p^e))$. For $j \in \{0, \ldots, 5\}$, a unit $t$, and an integer $e$, define $\mathcal R_{\mathfrak p,j,e}(t) = \sum_{v\in k_{\mathfrak p}^\times}\alpha_{\mathfrak p,j}(v)W_{\mathfrak p}(a(p^{e-2}t)wn(v/p))$. It vanishes for $e < 0$. For $e \ge 0$, $\mathcal R_{\mathfrak p,j,e}(t) = W_e\chi_{\mathfrak p}(t)^{4+2e}\sum_{v\in k_{\mathfrak p}^\times}\alpha_{\mathfrak p,j}(v)\chi_{\mathfrak p}(v)^4\psi_{\mathfrak p}(p^{e-1}t/v)$. (6.14) For $j = 1$, it vanishes for $e > 0$, while $\mathcal R_{\mathfrak p,1,0}(t) = \omega_{\mathfrak p}\chi_{\mathfrak p}(t)$, $|\omega_{\mathfrak p}| = 1$, […] (6.15) For all $j$, its magnitude at $e = 0$ is at most 1, and for $e > 0$ is at most $q_{\mathfrak p}^{1/2}|W_e|$. More precisely, for $e \ge 0$ put $s_{\mathfrak p,j,e} = \mathcal R_{\mathfrak p,j,e}(1)$ and choose the exponents modulo 6 by $b_{j,0} \equiv 8 - j$, $b_{j,e} \equiv 4 + 2e$ $(e > 0)$, $\mathcal R_{\mathfrak p,j,e}(t) = s_{\mathfrak p,j,e}\chi_{\mathfrak p}(t)^{b_{j,e}}$. (6.16)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 19, 28, 31–32, Lemma 6.2, (6.14)–(6.16), with the local sextic symbols and the masks (6.3) at one exterior prime (the finite-field part of the local Weyl calculation)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_digitSum_eq_mul_localSymbol_pow (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
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
    let Rsum : (P : Ideal (𝓞 F)) → ℕ → ℤ → F → ℂ := fun P j e₀ t =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        mask P j v * (if v = 0 then 0 else Wweyl P e₀ t v)
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P),
      let val := (⟨P, hP, hPe.1⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 F)).valuation F
      (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
        sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ val (y : F) = 1) ∧
      (∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
        val (g.gen I : F) = WithZero.exp (-(((normalizedFactors I).count P : ℕ) : ℤ))) ∧
      (∀ t t' : F, val t = 1 → val t' = 1 → lsym P (t * t') = lsym P t * lsym P t') ∧
      (∀ t : F, val t = 1 → lsym P t ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
        lsym P (y : F) = sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ k : ℕ, k ≠ 0 → ∀ (e₀ : ℤ) (t : F),
        Eloc P k e₀ t = mask P (k % 6) 0 * Wsph P e₀ t + Rsum P (k % 6) e₀ t) ∧
      (∀ j : ℕ, j ≠ 0 → mask P j 0 = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 → ∀ t : F, val t = 1 →
        Rsum P j e₀ t = Rsum P j e₀ 1 *
          lsym P t ^ (if (e₀ + 2).toNat = 0 then 8 + 5 * j else 4 + 2 * (e₀ + 2).toNat)) ∧
      (∀ e₀ : ℤ, 0 < e₀ + 2 → ∀ t : F, val t ≤ 1 → Rsum P 1 e₀ t = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 →
        ‖Rsum P j e₀ 1‖ ≤ βp (Ideal.absNorm P) (e₀ + 2).toNat) ∧
      (∀ j : ℕ, ‖mask P j 0‖ ≤ 1) ∧
      ‖gaussPhase g 2 P‖ ≤ 1 := by
  sorry

end ArtinPrimitiveRoots
