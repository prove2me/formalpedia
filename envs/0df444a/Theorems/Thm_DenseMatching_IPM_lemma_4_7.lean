-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_7
-- name    : DenseMatching.IPM.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:13.860423+00:00
-- url     : https://prove2.me/theorems/66a70820-0f83-4af5-801a-324b5d08dd5a
-- title:
--   Lemma 4.7, the per-step bounds (18) — Σ|ν̂ − ν|/(1 − |ν|) and Σ|log ĉ/c| + Σ|log f̂/f| are ≤ 10⁴(√m η + #sampled with p < 1) (anchor-count sentence: see HARD.md)
-- statement:
--   Consider a step by Equation (16) satisfying the hypotheses of Lemmas 4.4 and 4.6: on $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$, $\eta=10^{-5}$, $\alpha=10^7$), $f,c>0$ with $f_ec_e=\mu(1+\nu_e/10)$, $|\nu_e|<1$, the invariant $\psi(\nu)\le10^2m$, representatives $\bar\nu$ with Equation (4), $\|r\|_{(B^\top\mathrm{Diag}(f/c)B)^\dagger}\le10\eta\sqrt\mu$, $\Delta x$ as in Lemma 4.6, $\tilde f,\tilde\nu$ the Newton adjustment, and probabilities $p^s\le p\le1$. For every outcome of the sampling, with $\hat c,\hat f,\hat\mu$ of (16), $\hat\nu=10(\hat f\circ\hat c/\hat\mu-1)$, and $s=|\{e\ \text{sampled}:p_e<1\}|$ (an edge is sampled when $f^{\rm sample}_e\ne0$),
--   $$\sum_e\frac{|\hat\nu_e-\nu_e|}{1-|\nu_e|}\le10^4(\sqrt m\,\eta+s),\tag{18}$$
--   $$\sum_e\Big|\log\frac{\hat c_e}{c_e}\Big|+\sum_e\Big|\log\frac{\hat f_e}{f_e}\Big|\le10^4(\sqrt m\,\eta+s),$$
--   with $\log=\log_2$ (p. 7). These bound the number of anchor resets over the path.
--
--   This item is the per-step part of Lemma 4.7. The lemma's "Consequently" sentence (the total number of anchor resets over a sequence of accepted steps, $O(m+\sum_{\rm steps}(\sqrt m\eta+s))=O(n^2\log n)$) concerns the anchor-maintenance process of §4.1 over the run of the method; it is not stated here and is recorded in `HARD.md`.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - encoding: ‖v‖²_{(B⊤Diag(f/c)B)†}, the Moore–Penrose pseudoinverse of the tracked Laplacian → v ⬝ᵥ (lapPinv *ᵥ v) of the published WGraph with weights f/c (pinvNormSq); reason: same object for f, c > 0, which every statement assumes
--   - reading: Δµ in Lemma 4.6, the method's direction → Δµ = clippedDir η ν̄ for representatives ν̄ satisfying Equation (4); reason: Δµ is the clipped direction of Definition 4.2 on the representatives (Figure 4, Step 3(a)); Equation (4) is a standing invariant of Figure 3
--   - encoding: log (all logarithms base 2, p. 7) → Real.logb 2; reason: the paper's convention
--   - reading: 'the hypotheses of Lemmas 4.4 and 4.6' for a step of the method → the hypotheses of Lemma 4.6, the invariants ψ(ν) ≤ 10²m and Equation (4), and p^s ≤ p ≤ 1; the norm hypotheses of Lemma 4.4 are not assumed because Lemma 4.6(a) proves them; reason: the proof uses ψ(ν) ≤ 10²m as 'an invariant of Figure 3'; a fact the source proves is never added as a hypothesis
--   - encoding: every realization of the sampled correction → ∀ ω (any outcome of the coins); reason: the bounds are deterministic in the outcome
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 37, Lemma 4.7, Equation (18) and the inequality after it

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs
import Definitions.Def_DenseMatching_IPM_FlowLP

open Matrix

namespace DenseMatching.IPM

/-- Lemma 4.7, the per-step bounds (18) (p. 37). For a step by Equation (16) satisfying the
hypotheses of Lemmas 4.4 and 4.6 (on `K_{n/2,n/2}`, `n = 2k ≥ 2^20`, `m = k²`, under the invariants
`ψ(ν) ≤ 10²m` and Equation (4)), and for every outcome of the sampling with probabilities
`pˢ ≤ p ≤ 1`, with `s = |{e sampled : p_e < 1}|` (an edge is sampled when `f^sample_e ≠ 0`):
`∑_e |ν̂_e − ν_e|/(1 − |ν_e|) ≤ 10⁴(√m η + s)` and
`∑_e |log(ĉ_e/c_e)| + ∑_e |log(f̂_e/f_e)| ≤ 10⁴(√m η + s)` (`log = log₂`). The lemma's
"Consequently" sentence (the number of anchor resets over a sequence of steps) is not part of this
item. -/
theorem lemma_4_7 (k : ℕ) (hk : 2 ^ 19 ≤ k) (f c : KE k → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hf : ∀ e, 0 < f e) (hc : ∀ e, 0 < c e) (ν νbar : KE k → ℝ)
    (hdev : ∀ e, f e * c e = μ * (1 + ν e / 10)) (hν : ∀ e, |ν e| < 1)
    (hψ : potential ν ≤ 10 ^ 2 * (k : ℝ) ^ 2)
    (hrep : RepresentativesClose eta ν νbar)
    (hr : Real.sqrt (pinvNormSq k f c (residual k f)) ≤ 10 * eta * Real.sqrt μ)
    (dx : KV k → ℝ)
    (hdx : Real.sqrt (lapNormSq k f c (dx - pinvApply k f c
        (residual k f + (incK k)ᵀ *ᵥ (fun e => f e * clippedDir eta νbar e / 10)))) ≤
      1 / 20 * Real.sqrt (pinvNormSq k f c
        (residual k f + (incK k)ᵀ *ᵥ (fun e => f e * clippedDir eta νbar e / 10))))
    (p : KE k → ℝ)
    (hp : ∀ e, sparsityIntensity (2 * k) eta alpha νbar
        (newtonFlow (incK k *ᵥ dx) c (clippedDir eta νbar))
        (newtonNu ν (incK k *ᵥ dx) c (newtonFlow (incK k *ᵥ dx) c (clippedDir eta νbar))) e ≤ p e ∧
      p e ≤ 1)
    (ω : KE k → Bool) :
    let dmu := clippedDir eta νbar
    let Bdx := incK k *ᵥ dx
    let ft := newtonFlow Bdx c dmu
    let fs := sampledCorrection ft p ω
    let δ := shrink eta ((k : ℝ) ^ 2)
    let chat : KE k → ℝ := fun e => c e + Bdx e
    let fhat : KE k → ℝ := fun e => f e + f e * (dmu e / 10 - fs e)
    let νhat := deviation ((1 - δ) * μ) fhat chat
    let s : ℝ := ((Finset.univ.filter (fun e => fs e ≠ 0 ∧ p e < 1)).card : ℝ)
    ∑ e, |νhat e - ν e| / (1 - |ν e|) ≤ 10 ^ 4 * (Real.sqrt ((k : ℝ) ^ 2) * eta + s) ∧
      ∑ e, |Real.logb 2 (chat e / c e)| + ∑ e, |Real.logb 2 (fhat e / f e)| ≤
        10 ^ 4 * (Real.sqrt ((k : ℝ) ^ 2) * eta + s) := by sorry

end DenseMatching.IPM
