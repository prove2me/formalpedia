-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
-- name    : ArtinPrimitiveRoots.norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T10:53:03.951664+00:00
-- url     : https://prove2.me/theorems/7f00ecca-5a77-440b-8d37-551e8fc3d7f1
-- title:
--   Goldmakher–Louvel's bilinear bounds for the four terms of the explicit formula for Σ₃, summed over coprime pairs of columns
-- statement:
--   Let $F$ be a number field, let $\iota : F \to \mathbb C$ be a ring homomorphism, let $\mathfrak m \ne 0$ be an ideal of $\mathcal O_F$, let $g$ be a system of allowed generators (`AllowedGen ι 𝔪`), and suppose that `GLW.PsiHyp 𝔪 (c₁ * c₂) (GLW.psiP g c₁ c₂)` holds for all ideals $\mathfrak c_1, \mathfrak c_2$ exterior to $\mathfrak m$ (bundle `Def_ArtinGLWeight`). Write $\omega(\mathfrak g)$ for the number of prime factors of $\mathfrak g$, $q$ for the absolute norm, and, for a finite set $C$ of columns and a complex function $z$, $\Sigma(G)$ for `GLW.PSnp C z G` and $Z$ for `GLW.Ztau C z`. In each case below, $C$ consists of ideals in `GLW.sqfRows 𝔪 Cmax`, and the term $G(\mathfrak c_1, \mathfrak c_2)$ is the corresponding bundle term for $\mathfrak c = \mathfrak c_1\mathfrak c_2$ and $\psi$ = `GLW.psiP g c₁ c₂`.
--
--   1. For $0 < \varepsilon < 1/2$ there is $K \ge 0$ such that for every $\mathfrak g \ne 0$ with $\mathfrak g\mathfrak m \ne 0$, every $C$ coprime to $\mathfrak g\mathfrak m$, all $z$, $M > 0$, $L$, and $\beta \ge 0$ with `sbBound ι 𝔪 g (Srow 𝔪 𝔤 L) C β`: $|\Sigma(\texttt{RPt})| \le K M^{\varepsilon}2^{\omega(\mathfrak g\mathfrak m)}\beta Z$.
--   2. For $0 < \varepsilon' < 1/2$ there is $K \ge 0$ such that for every $\mathfrak g$, $C$, $z$, $M > 0$, $L'$, $\beta \ge 0$ and $C_{\min} > 0$ with $C_{\min} \le q_{\mathfrak c}$ on $C$ and `sbBound ι 𝔪 g (sqfRows 𝔪 L') C β`: $|\Sigma(\texttt{DPt})| \le K M^{1-\varepsilon'}2^{\omega(\mathfrak g)}\beta C_{\min}^{-(1-2\varepsilon')}Z$.
--   3. For $\sigma_1 \ge 1$ there is $K \ge 0$ such that for every $\mathfrak g \ne 0$, $C$, $z$, $M > 0$ and $L' > 0$: $|\Sigma(\texttt{DQt})| \le K M^{-\sigma_1}q_{\mathfrak g}^{\sigma_1}2^{\omega(\mathfrak g)}\max(C_{\max}, 1)^{1+2\sigma_1}L'^{-(\sigma_1 - 1/2)}\,\#C\,Z$.
--   4. For every $\mathfrak g$, $C$, $z$, $M$, $L, L' > 0$, every $\beta_f \ge 0$ with `sbBound ι 𝔪 g (sqfRows 𝔪 Y) C (βf Y)` for all $Y$, and all $N_B, B_m \ge 0$ such that, for every set $f$ of prime factors of $\mathfrak g$ with $Y_0 = \min(L'/q_{\mathfrak p_f}, L)$, $Y_1 = \max(L'/q_{\mathfrak p_f}, L)$ and $\mathfrak p_f$ = `pideal f`, `nblk Y₀ Y₁` $\le N_B$ and $(2^kY_0)^{-1/2}\beta_f(2^{k+1}Y_0) \le B_m$ whenever $2^kY_0 \le 2Y_1$:
--   $$|\Sigma(\texttt{TTt})| \le \big|\texttt{R0 F 1}/2\cdot M^{1/2}\,\texttt{Wm}(1/2)\big|\,2^{\omega(\mathfrak m)}\,4^{\omega(\mathfrak g)}\,N_B\cdot 2B_mZ.$$
--
--   These are the bounds of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, §§5–7, for the four terms of the explicit formula for $\Sigma_3$, here for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. The hypotheses `sbBound` are their bilinear-form bounds $B_2$ for the rows of each term. The terms and the route differ from theirs, as the bundle's formalization note says.
--
--   It is a cut for `exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le` (their Proposition 5.2), together with `tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt` and `exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation`.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, §§5–7, the bilinear bounds for the four terms of the explicit formula summed over coprime pairs of columns (a cut for Proposition 5.2)

import Mathlib
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinGLWeight

namespace ArtinPrimitiveRoots

open NumberField

theorem norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
    (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (g : AllowedGen ι 𝔪)
    (hψ : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      GLW.PsiHyp 𝔪 (c₁ * c₂) (GLW.psiP g c₁ c₂)) :
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ → 𝔤 * 𝔪 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      (∀ c ∈ C, c ⊔ 𝔤 * 𝔪 = ⊤) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L β : ℝ), 0 < M → 0 ≤ β →
      GLW.sbBound ι 𝔪 g (GLW.Srow 𝔪 𝔤 L) C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.RPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L ε)‖ ≤
          K * M ^ ε * 2 ^ (GLW.primesOf (𝔤 * 𝔪)).card * β * GLW.Ztau C z) ∧
    (∀ ε' : ℝ, 0 < ε' → ε' < 1 / 2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' β Cmin : ℝ), 0 < M → 0 ≤ β → 0 < Cmin →
      (∀ c ∈ C, Cmin ≤ (Ideal.absNorm c : ℝ)) →
      GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 L') C β →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DPt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' ε')‖ ≤
          K * M ^ (1 - ε') * 2 ^ (GLW.primesOf 𝔤).card * β * Cmin ^ (-(1 - 2 * ε')) *
            GLW.Ztau C z) ∧
    (∀ σ₁ : ℝ, 1 ≤ σ₁ → ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ →
      ∀ (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ), (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L' : ℝ), 0 < M → 0 < L' →
        ‖GLW.PSnp C z (fun c₁ c₂ => GLW.DQt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L' σ₁)‖ ≤
          K * M ^ (-σ₁) * (Ideal.absNorm 𝔤 : ℝ) ^ σ₁ * 2 ^ (GLW.primesOf 𝔤).card *
            (max Cmax 1) ^ (1 + 2 * σ₁) * L' ^ (-(σ₁ - 1 / 2)) * C.card * GLW.Ztau C z) ∧
    (∀ (𝔤 : Ideal (𝓞 F)) (C : Finset (Ideal (𝓞 F))) (Cmax : ℝ),
      (∀ c ∈ C, c ∈ GLW.sqfRows 𝔪 Cmax) →
      ∀ (z : Ideal (𝓞 F) → ℂ) (M L L' : ℝ), 0 < L → 0 < L' →
      ∀ βf : ℝ → ℝ, (∀ Y, 0 ≤ βf Y) → (∀ Y, GLW.sbBound ι 𝔪 g (GLW.sqfRows 𝔪 Y) C (βf Y)) →
      ∀ NB Bm : ℝ, 0 ≤ NB → 0 ≤ Bm →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset,
        (GLW.nblk (min (L' / Ideal.absNorm (GLW.pideal f)) L)
          (max (L' / Ideal.absNorm (GLW.pideal f)) L) : ℝ) ≤ NB) →
      (∀ f ∈ (GLW.primesOf 𝔤).powerset, ∀ k : ℕ,
        2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L ≤
          2 * max (L' / Ideal.absNorm (GLW.pideal f)) L →
        (2 ^ k * min (L' / Ideal.absNorm (GLW.pideal f)) L) ^ (-(1 / 2 : ℝ)) *
          βf (2 ^ (k + 1) * min (L' / Ideal.absNorm (GLW.pideal f)) L) ≤ Bm) →
      ‖GLW.PSnp C z (fun c₁ c₂ => GLW.TTt 𝔪 𝔤 (c₁ * c₂) (GLW.psiP g c₁ c₂) M L L')‖ ≤
        ‖GLW.R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * GLW.Wm (1 / 2)‖ *
          2 ^ (GLW.primesOf 𝔪).card * (4 : ℝ) ^ (GLW.primesOf 𝔤).card *
          (NB * (2 * Bm * GLW.Ztau C z))) := by
  sorry

end ArtinPrimitiveRoots
