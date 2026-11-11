-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_20
-- name    : DPCutRelease.Main.lemma_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:14:12.661194+00:00
-- url     : https://prove2.me/theorems/47e8714e-8c6f-49cd-8693-eaee268087ad
-- title:
--   Lemma 20 — AggregateWitnesses returns valid over/under-estimation witnesses and all-cut accuracy on r* w.p. 1 − β_GE
-- statement:
--   Let $0<\gamma<1$, $K=\Theta(\log(n/\beta_{GE}))$, $\tau_1=\log(1/\beta_1)/\varepsilon_1$, $\beta_1=\beta_\chi=\beta_{GE}/(4n^2K)$ (Algorithm 2's parameters from $\varepsilon_{GE},\delta_{GE},\beta_{GE}\in(0,1)$). Given nonnegative edge weights $w$ with $w_e\le U$ for every $e$ and a nonnegative partial estimate $h$, let $(g^+,g^-,r^*)=\mathrm{AggregateWitnesses}(w,h,\gamma)$. Then with probability at least $1-\beta_{GE}$:
--   - $\langle h,g^+\rangle\ge(1+\gamma)\langle w,g^+\rangle$;
--   - $\langle h,g^-\rangle\le(1-\gamma)\langle w,g^-\rangle$;
--   - for every cut $S$ simultaneously,
--   $$(1-\gamma)\langle w,c_S\odot r^*\rangle-B\le\langle h,c_S\odot r^*\rangle\le(1+\gamma)\langle w,c_S\odot r^*\rangle+B,$$
--   where $B=\Theta(\tau_1+\lambda n\log n+nU)$.
--
--   The $\Theta$-constants are read in region form (Lemma 17), and $B=c_B(\tau_1+\lambda n\log n+nU)$ with $c_B>0$ chosen after the constants.
--
--   **Formalization Note.** `aggregate (fwParams θ n εGE δGE βGE) w h γ`; `.1, .2.1, .2.2` are $g^+,g^-,r^*$.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: "B = Θ(τ₁ + λ n log n + nU)" → B = c_B·(τ₁ + λ n log n + nU) with ∃ c_B > 0 after the constants θ, before n, γ, w, h, U; reason: B is a bound of the analysis; its constant may depend on the algorithm’s constants but on nothing else
--   - reading: ε₁, k, λ of the invocation (left implicit; Algorithm 2 line 1) → fwParams θ n ε_GE δ_GE β_GE with ε_GE, δ_GE, β_GE ∈ (0, 1); reason: the parameters Algorithm 2 sets for its inputs
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 28, Lemma 20

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 20 (p. 28): for all sufficiently large Θ-constants there is `c_B > 0` such that for
`0 < γ < 1`, `ε_GE, δ_GE, β_GE ∈ (0, 1)`, nonnegative `w ≤ U` and `h`, with probability at least
`1 − β_GE` the output `(g⁺, g⁻, r*)` of AggregateWitnesses satisfies `⟨h, g⁺⟩ ≥ (1+γ)⟨w, g⁺⟩`,
`⟨h, g⁻⟩ ≤ (1−γ)⟨w, g⁻⟩` and, for every cut, `(1−γ)⟨w, c_S ⊙ r*⟩ − B ≤ ⟨h, c_S ⊙ r*⟩ ≤
(1+γ)⟨w, c_S ⊙ r*⟩ + B` with `B = c_B(τ₁ + λ n log n + nU)`. -/
theorem lemma_20 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∃ cB : ℝ, 0 < cB ∧ ∀ (n : ℕ) (γ epsGE deltaGE betaGE U : ℝ) (w h : EdgeVec n),
        0 < γ → γ < 1 → 0 < epsGE → epsGE < 1 → 0 < deltaGE → deltaGE < 1 →
        0 < betaGE → betaGE < 1 → Nonneg w → Nonneg h → (∀ e, w e ≤ U) →
        noiseLaw {ω | ¬ ((1 + γ) * dot w (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).1 ≤
              dot h (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).1 ∧
            dot h (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.1 ≤
              (1 - γ) * dot w (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.1 ∧
            ∀ S : Finset (Fin n),
              (1 - γ) * dot w (cutVec S * (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.2)
                  - cB * ((fwParams θ n epsGE deltaGE betaGE).tau1 +
                    (fwParams θ n epsGE deltaGE betaGE).lam * n * Real.log n + n * U) ≤
                dot h (cutVec S * (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.2) ∧
              dot h (cutVec S * (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.2) ≤
                (1 + γ) * dot w (cutVec S * (aggregate (fwParams θ n epsGE deltaGE betaGE) w h γ ω).2.2)
                  + cB * ((fwParams θ n epsGE deltaGE betaGE).tau1 +
                    (fwParams θ n epsGE deltaGE betaGE).lam * n * Real.log n + n * U))}
          ≤ ENNReal.ofReal betaGE := by sorry

end DPCutRelease.Main
