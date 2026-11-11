-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_18
-- name    : DPCutRelease.Main.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:49.715892+00:00
-- url     : https://prove2.me/theorems/fb742843-02c1-47b1-87fc-71155d6dc1ad
-- title:
--   Lemma 18 — privacy of Algorithm 1 (CutRelease) is (ε, δ)
-- statement:
--   For $0<\varepsilon\le1$ and $0<\delta<1$, with $\varepsilon_2=\frac\varepsilon{2T_1}$, $\varepsilon_{GE}=\frac\varepsilon{4T_1\sqrt{2T_2\log(2T_1/\delta)}}$, $\delta_{GE}=\frac\delta{2T_1T_2}$ and the other parameters of Algorithm 1, line 1, Algorithm 1 is $(\varepsilon,\delta)$ edge-DP: for adjacent nonnegative $w,w'$ and every measurable set $A$ of outputs,
--   $$\Pr[\mathrm{CutRelease}(w)\in A]\le e^{\varepsilon}\Pr[\mathrm{CutRelease}(w')\in A]+\delta .$$
--   This holds for every $n$, every public bound $U$, $\gamma\in(0,1)$ and $\beta\in(0,1)$, and for all sufficiently large $\Theta$-constants (region form as in Lemma 17).
--
--   **Formalization Note.** `cutRelease (a1Params θ n U γ ε δ β)`.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: "Algorithm 1 is (ε, δ)-DP" (Algorithm 1 takes n, U, γ, β as public inputs) → for every n, U, 0 < γ < 1 and 0 < β < 1; reason: the lemma fixes only ε, δ; γ ∈ (0,1) is Algorithm 4’s range and covers Algorithm 1’s γ ≤ 1/4
--   - generalization: Algorithm 1's input is a bounded graph (wₑ ≤ U, input line p. 13 and §3.3 p. 19) → every nonnegative w, U any real (it enters only through T₁ and M_stop); reason: the privacy proof (pp. 26–27) uses only ‖w − w′‖₁ ≤ 1 and the parameter choices, never wₑ ≤ U; on U-bounded w the statement is the printed one
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 26, Lemma 18

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 18 (Privacy of Algorithm 1, p. 26): for all sufficiently large Θ-constants, for
`0 < ε ≤ 1`, `0 < δ < 1` (and every `n`, `U`, `γ ∈ (0, 1)`, `β ∈ (0, 1)`), Algorithm 1 with the
parameters of its line 1 is `(ε, δ)` edge-DP. -/
theorem lemma_18 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∀ (n : ℕ) (U γ ε δ β : ℝ), 0 < γ → γ < 1 → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        0 < β → β < 1 →
        IsEdgeDPFun noiseLaw (fun (w : EdgeVec n) ω => cutRelease (a1Params θ n U γ ε δ β) w ω)
          ε δ := by sorry

end DPCutRelease.Main
