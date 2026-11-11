-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_17
-- name    : DPCutRelease.Main.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:45.626526+00:00
-- url     : https://prove2.me/theorems/9aebcf1c-31ee-4aa6-b4d0-1c4f2e3e99d4
-- title:
--   Lemma 17 — privacy of Algorithm 3: each invocation of AggregateWitnesses in Algorithm 1 is (ε_GE, δ_GE)-DP
-- statement:
--   Fix $\varepsilon_{GE},\delta_{GE},\beta_{GE}\in(0,1)$ and let $\varepsilon_1=\frac{\varepsilon_{GE}}{320K(1+\log(2/\delta_{GE}))}$, $\delta_1=\frac{\delta_{GE}}{20n^2K}$, $k=\Theta(\log\frac n{\beta_\chi\delta_1})$, $\beta_\chi=\frac{\beta_{GE}}{4n^2K}$ and $\lambda=\Theta(\frac1{\varepsilon_1}\log\frac n{\beta_{GE}\delta_{GE}})$ (with $K=\Theta(\log\frac n{\beta_{GE}})$ of Algorithm 2). Then each invocation of Algorithm 3 in Algorithm 1 with input $(w_i,h_i,\gamma)$, $w_i=a_i\odot w$, is $(\varepsilon_{GE},\delta_{GE})$-differentially private: for every mask $a\in[0,1]^{\binom n2}$, every candidate $h$ and $0<\gamma<1$, the mechanism
--   $$w\longmapsto\mathrm{AggregateWitnesses}(a\odot w,\,h,\,\gamma)$$
--   is $(\varepsilon_{GE},\delta_{GE})$ edge-DP. The $\Theta(\cdot)$ constants are read as: there are $c_0,f,g$ such that the claim holds for every constant structure with $c_k,c_K,c_{T_1}\ge c_0$, $c_\lambda\ge f(c_k,c_K,c_{T_1})$, $c_{stop}\ge g(\dots)$.
--
--   **Formalization Note.** `aggregate (fwParams θ n εGE δGE βGE)`, `noiseLaw`, `IsEdgeDPFun`.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: "each invocation of Algorithm 3 in Algorithm 1 with input (wᵢ, hᵢ, γ)" at any common history → for every mask a ∈ [0,1]^E, every h and every γ ∈ (0,1): w ↦ aggregate (a ⊙ w) h γ; reason: at a common history the mask aᵢ ∈ [0,1] and hᵢ are fixed; Algorithm 4 states γ ∈ (0,1), and Algorithm 1 runs with γ ≤ 1/4
--   - generalization: Algorithm 1's input is a bounded graph (wₑ ≤ U, input line p. 13 and §3.3 p. 19) and the candidate hᵢ is nonnegative → every nonnegative w with no bound, and every h ∈ ℝ^E; reason: the privacy proof (pp. 23–26) uses only ‖w − w′‖₁ ≤ 1, aᵢ ∈ [0,1] and γ < 1, never wₑ ≤ U or the sign of h; on U-bounded w and nonnegative h the statement is the printed one
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 23, Lemma 17

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 17 (Privacy of Algorithm 3, p. 23): for all sufficiently large Θ-constants, for every
`ε_GE, δ_GE, β_GE ∈ (0, 1)`, `γ ∈ (0, 1)`, mask `a ∈ [0,1]^{(n choose 2)}` and candidate `h`, the
invocation `w ↦ AggregateWitnesses(a ⊙ w, h, γ)` (Algorithm 2 parameters of line 1) is
`(ε_GE, δ_GE)` edge-DP. -/
theorem lemma_17 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∀ (n : ℕ) (γ epsGE deltaGE betaGE : ℝ) (a h : EdgeVec n), 0 < γ → γ < 1 →
        0 < epsGE → epsGE < 1 → 0 < deltaGE → deltaGE < 1 → 0 < betaGE → betaGE < 1 →
        (∀ e, 0 ≤ a e ∧ a e ≤ 1) →
        IsEdgeDPFun noiseLaw
          (fun w ω => aggregate (fwParams θ n epsGE deltaGE betaGE) (a * w) h γ ω)
          epsGE deltaGE := by sorry

end DPCutRelease.Main
