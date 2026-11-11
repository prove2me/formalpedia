-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_6
-- name    : DenseMatching.IPM.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:34.342197+00:00
-- url     : https://prove2.me/theorems/8f356fdc-32e1-411c-8bf9-871048b8d926
-- title:
--   Lemma 4.6 — the Newton step: bounds (a), the exact deviation update (12) for every sampled correction (b), and the residual bounds (17) (c)
-- statement:
--   On $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$, $\eta=10^{-5}$), let $f,c>0$ with $\mu_e=f_ec_e=\mu(1+\nu_e/10)$, $|\nu_e|<1$, $\mu>0$, let $\bar\nu$ satisfy Equation (4) and $\Delta\mu$ be its clipped direction, and let $r=B^\top f-d$ with $\|r\|_{(B^\top\mathrm{Diag}(f/c)B)^\dagger}\le10\eta\sqrt\mu$. Write $M=B^\top\mathrm{Diag}(f/c)B$ and $b=r+B^\top\mathrm{Diag}(f)\Delta\mu/10$, and let $\Delta x$ satisfy
--   $$\|\Delta x-M^\dagger b\|_M\le\tfrac1{20}\|b\|_{M^\dagger}.$$
--   Let $\tilde f=(B\Delta x)\circ(1+\Delta\mu/10)/(c+B\Delta x)$ and $\tilde\nu=10(1+\nu/10)\circ(1+B\Delta x/c)\circ\tilde f$. Then:
--
--   (a) $\|B\Delta x/c\|_2\le15\eta$, $\|\tilde f\|_2\le15\eta$ and $\|\tilde\nu\|_2\le2\cdot10^2\eta$;
--
--   (b) for every sampled correction $f^{\rm sample}$ of $\tilde f$ (Equation (11), probabilities $p^s\le p\le1$, every outcome), the update
--   $$\hat c=c+B\Delta x,\qquad\hat f=f+\mathrm{Diag}(f)(\Delta\mu/10-f^{\rm sample}),\qquad\hat\mu=(1-\delta)\mu\tag{16}$$
--   has deviations $\hat\nu=10(\hat f\circ\hat c/\hat\mu-1)$ satisfying Equation (12) exactly, with $\nu^\circ$ the sampling error of $\tilde\nu$ and $\delta=10^{-3}\eta/\sqrt m$;
--
--   (c) $\|b-B^\top\mathrm{Diag}(f)\tilde f\|_{M^\dagger}\le(\eta+10^3\eta^2)\sqrt\mu$ (17), and the residual of $\hat f$ is exactly $\hat r=b-B^\top\mathrm{Diag}(f)f^{\rm sample}$.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - encoding: ‖v‖²_{(B⊤Diag(f/c)B)†}, the Moore–Penrose pseudoinverse of the tracked Laplacian → v ⬝ᵥ (lapPinv *ᵥ v) of the published WGraph with weights f/c (pinvNormSq); reason: same object for f, c > 0, which every statement assumes
--   - reading: Δµ in Lemma 4.6, the method's direction → Δµ = clippedDir η ν̄ for representatives ν̄ satisfying Equation (4); reason: Δµ is the clipped direction of Definition 4.2 on the representatives (Figure 4, Step 3(a)); Equation (4) is a standing invariant of Figure 3
--   - encoding: 'for a sampled correction f^sample of f̃ (11)' → for every p with p^s ≤ p ≤ 1 and every outcome ω of the coins, f^sample = sampledCorrection f̃ p ω; reason: (b) and the last claim of (c) are identities that hold on every outcome
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 35, Lemma 4.6

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs
import Definitions.Def_DenseMatching_IPM_FlowLP

open Matrix

namespace DenseMatching.IPM

/-- Lemma 4.6 (p. 35). On `K_{n/2,n/2}` (`n = 2k ≥ 2^20`, `m = k²`, `η = 10⁻⁵`), let `f, c > 0`
with `μ_e = f_e c_e = μ(1 + ν_e/10)`, `|ν_e| < 1`, representatives `ν̄` satisfying Equation (4),
`Δμ` the clipped direction of `ν̄`, and `r = B⊤f − d` with `‖r‖_{(B⊤Diag(f/c)B)†} ≤ 10η√μ`. Let `Δx`
solve `B⊤Diag(f/c)B Δx = b := r + B⊤Diag(f)Δμ/10` up to
`‖Δx − (B⊤Diag(f/c)B)† b‖_{B⊤Diag(f/c)B} ≤ (1/20) ‖b‖_{(B⊤Diag(f/c)B)†}`, and let
`f̃ = (BΔx) ∘ (1 + Δμ/10)/(c + BΔx)`, `ν̃ = 10(1 + ν/10) ∘ (1 + BΔx/c) ∘ f̃`. Then
(a) `‖BΔx/c‖₂, ‖f̃‖₂ ≤ 15η` and `‖ν̃‖₂ ≤ 2·10²η`;
(b) for every sampled correction `f^sample` of `f̃` (Equation (11), probabilities `pˢ ≤ p ≤ 1`), the
update (16) `ĉ = c + BΔx`, `f̂ = f + Diag(f)(Δμ/10 − f^sample)`, `μ̂ = (1 − δ)μ` has deviations
satisfying Equation (12) exactly;
(c) `‖b − B⊤Diag(f) f̃‖_{(B⊤Diag(f/c)B)†} ≤ (η + 10³η²)√μ`, and the residual of `f̂` is exactly
`b − B⊤Diag(f) f^sample`. -/
theorem lemma_4_6 (k : ℕ) (hk : 2 ^ 19 ≤ k) (f c : KE k → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hf : ∀ e, 0 < f e) (hc : ∀ e, 0 < c e) (ν νbar : KE k → ℝ)
    (hdev : ∀ e, f e * c e = μ * (1 + ν e / 10)) (hν : ∀ e, |ν e| < 1)
    (hrep : RepresentativesClose eta ν νbar)
    (hr : Real.sqrt (pinvNormSq k f c (residual k f)) ≤ 10 * eta * Real.sqrt μ)
    (dx : KV k → ℝ)
    (hdx : Real.sqrt (lapNormSq k f c (dx - pinvApply k f c
        (residual k f + (incK k)ᵀ *ᵥ (fun e => f e * clippedDir eta νbar e / 10)))) ≤
      1 / 20 * Real.sqrt (pinvNormSq k f c
        (residual k f + (incK k)ᵀ *ᵥ (fun e => f e * clippedDir eta νbar e / 10)))) :
    let dmu := clippedDir eta νbar
    let b := residual k f + (incK k)ᵀ *ᵥ (fun e => f e * dmu e / 10)
    let Bdx := incK k *ᵥ dx
    let ft := newtonFlow Bdx c dmu
    let νt := newtonNu ν Bdx c ft
    let δ := shrink eta ((k : ℝ) ^ 2)
    (l2norm (fun e => Bdx e / c e) ≤ 15 * eta ∧ l2norm ft ≤ 15 * eta ∧
        l2norm νt ≤ 2 * 10 ^ 2 * eta) ∧
      Real.sqrt (pinvNormSq k f c (b - (incK k)ᵀ *ᵥ (fun e => f e * ft e))) ≤
        (eta + 10 ^ 3 * eta ^ 2) * Real.sqrt μ ∧
      ∀ p : KE k → ℝ, (∀ e, sparsityIntensity (2 * k) eta alpha νbar ft νt e ≤ p e ∧ p e ≤ 1) →
        ∀ ω : KE k → Bool,
          let fs := sampledCorrection ft p ω
          let chat : KE k → ℝ := fun e => c e + Bdx e
          let fhat : KE k → ℝ := fun e => f e + f e * (dmu e / 10 - fs e)
          (∀ e, deviation ((1 - δ) * μ) fhat chat e - ν e =
            ((1 + ν e / 10) * dmu e - samplingErrorNu ft νt p ω e + δ * (ν e + 10)) / (1 - δ)) ∧
          residual k fhat = b - (incK k)ᵀ *ᵥ (fun e => f e * fs e) := by sorry

end DenseMatching.IPM
