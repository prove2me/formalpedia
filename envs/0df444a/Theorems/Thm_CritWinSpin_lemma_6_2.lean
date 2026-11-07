-- Prove2me | Theorems.Thm_CritWinSpin_lemma_6_2
-- name    : CritWinSpin.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:21.234493+00:00
-- url     : https://prove2.me/theorems/c2c86eba-5e89-4ced-8e8b-28118423a8e3
-- title:
--   Lemma 6.2, p.22 — tied clouds, the tail of $D_y$ and $\mathbb E_{\nu_y}[e^{D_y}]$ under (32)
-- statement:
--   Let $\bar W=\max\{1,W\}$ with $W=\mathrm{wd}(J_0,h_0)$. There is $C_*>0$ depending only on $\rho$ such that for any $L\ge n$, if
--   $$R=r\theta\hat u^2\ge C_*n\bar W^2[n\log(r+1)+L+1],$$
--   then for every $y\in\{\pm1\}^n$:
--
--   1. $\mathbb P_{\nu_y}(\exists i:M_i=0)\le e^{-L}$;
--   2. $\mathbb E_{\nu_y}[e^{|D_y|}1_{\{|D_y|>1\}}]\le e^{-L}$;
--   3. $e^{-1}(1-e^{-L})\le\mathbb E_{\nu_y}[e^{D_y}]\le e+e^{-L}$.
--
--   The hypotheses of §6.1 hold throughout: $n,r\ge1$, $J_0$ symmetric with zero diagonal, $\theta\in(0,\theta_0]$ and $\hat u$ with (28). These bounds make the rejection sampling of $\hat L_{T,k}$ accurate and efficient.
--
--   Differences from the source:
--   - reading: the lemma states only L ≥ n and (32); the rest is in §6.1 → explicit hypotheses n, r ≥ 1, J₀ symmetric with zero diagonal, θ ∈ (0, θ₀], and û with (28); reason: §6.1 (pp.20–21) and the proof use them: zero diagonal in (35), u from Lemma 3.1(ii)
--   - encoding: θ₀ of Lemma 3.1(ii) → ∃ θ₀ > 0 together with C*; reason: θ₀ in Lemma 3.1(ii) is itself existential and may be decreased, which the Berry–Esseen step on p.23 needs
--   - generalization: û dyadic → û rational with (28); reason: the bounds (28) are all the proof uses, and a dyadic û is rational
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 6.2, p.22, eqs. (32), (33); §6.1, pp.20–21

import Mathlib
import Definitions.Def_CritWinSpin_nuPm
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 6.2** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.22). With
`W̄ = max{1, W}`, there is `C* > 0` depending only on `ρ` such that for `L ≥ n`, if
`R = rθû² ≥ C* n W̄² [n log(r + 1) + L + 1]`, eq. (32), then for every `y`:
(i) `P_{ν_y}(∃i : M_i = 0) ≤ e^{−L}`; (ii) `E_{ν_y}[e^{|D_y|} 1{|D_y| > 1}] ≤ e^{−L}`, eq. (33);
(iii) `e^{−1}(1 − e^{−L}) ≤ E_{ν_y}[e^{D_y}] ≤ e + e^{−L}`.

**Formalization Note.** The hypotheses of §6.1 are written out: `n, r ≥ 1`; `H` symmetric with zero diagonal
and `W = wd(J₀, h₀)`; `θ ∈ (0, θ₀]` with `θ₀` of Lemma 3.1(ii), so that `u` exists; `û` with (28). -/
theorem lemma_6_2 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ θ₀ Cₛ : ℝ, 0 < θ₀ ∧ 0 < Cₛ ∧
      ∀ (n r : ℕ) (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (θ : ℝ) (û : ℚ) (L : ℝ),
        1 ≤ n → 1 ≤ r → J₀.IsSymm → (∀ i, J₀ i i = 0) → 0 < θ → θ ≤ θ₀ → IsUhat S θ r û →
        (n : ℝ) ≤ L →
        (r : ℝ) * θ * (û : ℝ) ^ 2 ≥
          Cₛ * (n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 *
            ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) →
        ∀ y : BinCfg n,
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0)) ≤ Real.exp (-L) ∧
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
                (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))) ≤ Real.exp (-L) ∧
          Real.exp (-1) * (1 - Real.exp (-L)) ≤
            (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              Real.exp (Dy J₀ h₀ (û : ℝ) y σ)) ∧
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              Real.exp (Dy J₀ h₀ (û : ℝ) y σ)) ≤ Real.exp 1 + Real.exp (-L) := by sorry

end CritWinSpin
