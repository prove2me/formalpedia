-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-18T12:12:51.146782+00:00
-- url     : https://prove2.me/theorems/8b3180bd-123f-42a8-af68-45f42a2a3cf3
-- title:
--   Proposition 5.1 of OpenAI's Primitive roots paper in coordinates — the forward and the Weyl-reflected Fourier expansions of the cubic theta function differ by a radial function
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`). The local symbols $\chi_P(t)$, $\psi_P$, $W_P(a(p^et))$, the masks $\alpha_{P,j}$, the per-digit Weyl values and $E_P$ are the `let`s of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`, with the same definitions. The model `SModel 𝔪 k` of $F_S^\times$, its embedding `sEmb` and the class group `SFinCls 𝔪 k` are those of the bundle `Def_ArtinHeckeSModel`; a point $y$ has coordinates $y_1(w) = \log|y_w|_w$, $y_2(w) = \arg y_w$ and finite part $y_3$.
--
--   There is $k_0$ such that for every level $k \ge k_0$ there are:
--   - a measurable $\kappa : \mathbb R \to \mathbb R$ with $\kappa \ge 0$, constants $c_\kappa, A_\kappa, \alpha > 0$ with $\int_0^\infty \kappa(t)t^{s-1}\,dt = c_\kappa A_\kappa^s\,\Gamma(s+5/6)\Gamma(s+7/6)$ (absolutely convergent) for $\operatorname{Re}s > -5/6$, and for every $N > 0$ a $C$ with $\kappa(t) \le C\min(t^\alpha, t^{-N})$ for $t > 0$;
--   - for every $m : W \to \mathbb Z$ with values $\pm1$, a function $F_m : $ `SFinCls 𝔪 k` $\times$ `SModel 𝔪 k` $\to \mathbb C$, measurable in the second variable, and $b_f \ge 0$ on `SFin 𝔪 k` with $\sum_y b_f(y)\,|y|^\sigma < \infty$ (`SFin.norm`) for every $\sigma \ge -\alpha$, such that $s \mapsto F_m(c, y + s\,e_w)$ is of class $C^2$ for every place $w$ ($e_w$ moves the coordinate $y_1(w)$), and for every $N > 0$ there is $C$ with $\big|(d/ds)^jF_m(c, y + s\,e_w)\big|_{s=0}\big| \le C\prod_{w'}\min(e^{\alpha y_1(w')}, e^{-Ny_1(w')})\,b_f(y_3)$ for $j \le 2$, all $w, c, y$;
--
--   such that for every exterior ideal $\mathfrak b$, with $b$ = `g.gen 𝔟`, the function
--   $$D(y) = \sum_{(z,\gamma)} \mathrm{coef}(z)\,f^+\big(\gamma\,m_z\cdot y\big) - \sum_{(z,\gamma)} E(z)\,F_m\big([\nu_z],\ \gamma\,\nu_z / y\big)$$
--   on `SModel 𝔪 k` satisfies $D(y + \text{rotation by }\varphi\text{ at } w) = D(y)$ for every infinite place $w$, angle $\varphi$ and $y$. Here the sums (`tsum`s) run over $z \in$ `RowClass 𝔪` and $\gamma \in U_S^6$; $m_z$ = `rowElt g z`; $\nu_z = m_z/b^2$; products and quotients by $y$ are sums and differences in `SModel` after `sEmb`; $[\nu]$ is the class of the finite part of `sEmb ν` in `SFinCls 𝔪 k`;
--   - $f^+(y) = \prod_w e^{i m_w y_2(w)}\,\kappa(e^{y_1(w)})$ if $y_3 = 0$, and $0$ otherwise;
--   - $\mathrm{coef}(z) = \chi_{\mathfrak b}(m_z)\prod_{P \mid \mathfrak z}W_P(a(m_z))$, with $\chi_{\mathfrak b}$ = `residueSymbol ι 𝔪 𝔟`, $\mathfrak z = z_1$ and $W_P(a(m_z))$ the spherical value at $v_P(\mathfrak z)$ and the unit part $m_z p^{-v_P(\mathfrak z)}$;
--   - $E(z) = \prod_{P \mid \mathfrak z\mathfrak b}E_P\big(v_P(\nu_z),\,\nu_z p^{-v_P(\nu_z)}\big)$, the exterior product of `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`.
--
--   This is a cut for `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`: together with `exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six` and `exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol` it gives that statement, and that reduction is proved in Lean.
--
--   In the paper this is Proposition 5.1 (pp. 18–20), with the rational automorphy $\theta_\upsilon(g) = \theta_\upsilon(wg)$, evaluated at the points $g(y, \boldsymbol v)$ of §6.1 (p. 28) and masked over the digits. The forward sum is the nonconstant Fourier expansion (5.3) with the factorization (5.2) and the exterior values (5.6), against the chosen $S$-Whittaker function (5.14), $\kappa(t) = tK_{1/3}(c\sqrt t)$ up to a constant. The reflected sum is the expansion at $wg(y, \boldsymbol v)$, with the per-digit values of the proof of Lemma 6.2 and the $S$-factor $\mathcal C_S(\nu, y^{-1})W_{w}(a(\nu/y))$; $F_m$ obeys the bounds (5.12) and (5.13) of the Whittaker functions. $D$ is the difference of the two constant terms, which are radial by Proposition 5.1(iii). The paper takes the theta representation from Kazhdan and Patterson, whose residue construction is [15, Theorem II.2.1, p. 118].
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 20: “The constant term of the automorphic theta function belongs to the Weyl-conjugate torus induction. In particular its dependence on a complex diagonal $a(y)$ is radial, also when the vector on its right has been acted on by a fixed compact element.” and p. 85: “The residue construction and restricted tensor product are [15, Theorem II.2.1, p. 118].”
--
--   **Formalization note.** The Fourier expansion over $\nu \in F^\times$ is written over $(z, \gamma) \in$ `RowClass 𝔪` $\times\ U_S^6$, i.e. over $\nu = \gamma m_z \in R \setminus 0$ (forward) and $\nu = \gamma\nu_z$ (reflected); the coefficients are written at $m_z$ and $\nu_z$, where $\gamma$ is a sixth power of an $S$-unit. The cover, the theta function and the constant terms do not appear: the statement is their consequence on the torus–digit family.
--
--   **Correction note.** This statement is `exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial` with `0 < N` added to both of its decay clauses (the bound on $\kappa$ and the bound on the derivatives of $F_m$). Without it the statement is false: `not_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial`.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 18–20, 23, 28, 85, Proposition 5.1 with the rational automorphy θ(g) = θ(wg), evaluated on the torus–digit family g(y, v) of §6.1 and masked over the digits: the forward and reflected nonconstant Fourier expansions differ by the radial difference of the constant terms (Kazhdan–Patterson, cited as [15, Theorem II.2.1]); a cut for exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeSModel

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
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
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (κ : ℝ → ℝ) (cκ Aκ α : ℝ), Measurable κ ∧ 0 < cκ ∧ 0 < Aκ ∧ 0 < α ∧ (∀ t, 0 ≤ κ t) ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (κ t : ℂ)) s ∧
        mellin (fun t => (κ t : ℂ)) s =
          (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
        ‖iteratedDeriv j (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
          C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) ∧
    ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
    let fp : SModel 𝔪 k → ℂ := fun y =>
      if y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
      else 0
    let coef : RowClass 𝔪 → ℂ := fun z =>
      residueSymbol ι 𝔪 𝔟 (rowElt g z) *
        ∏ P ∈ (normalizedFactors z.1.1).toFinset,
          Wsph P ((normalizedFactors z.1.1).count P : ℤ)
            ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
    let Ez : RowClass 𝔪 → ℂ := fun z =>
      (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
        Eloc P ((normalizedFactors 𝔟).count P)
          (((normalizedFactors z.1.1).count P : ℤ) -
            2 * ((normalizedFactors 𝔟).count P : ℤ))
          ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
            (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
              2 * ((normalizedFactors 𝔟).count P : ℤ)))))
    let D : SModel 𝔪 k → ℂ := fun y =>
      (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
        ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)
    ∀ (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
      D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y
  := by
  sorry

end ArtinPrimitiveRoots
