-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_lemma_5
-- name    : CoVaRMC.Batching.Supplement.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:13:23.197792+00:00
-- url     : https://prove2.me/theorems/d0feda16-c2aa-45f2-95a6-a2681ca9cbfc
-- title:
--   Lemma 5, pp. 15–16 (corrected: stated off the event g* = x) — P_ε/(2ε) → q₁ + q₂ as ε → 0⁺, Equation (23)
-- statement:
--   In the delta-gamma model with $\gamma_{1d}>0$, fix a level $x\in\mathbb R$ and a value $w$ of $W=(Z_1,\dots,Z_{d-1})$. Let $P_\varepsilon=\Pr\{|X-x|\le\varepsilon\mid W=w\}$, and let $q_\ell=f_d(r_\ell)/\lambda$ for $\ell=1,2$ when $x>g^*$ and $q_\ell=0$ when $x\le g^*$, where $g^*=g^*(w)$ is the minimum of $z\mapsto X(w,z)$, $r_1<r_2$ are the roots of $X(w,z)=x$, $\lambda=|g'(r_\ell)|$, and $f_d$ is the standard normal density. If $g^*(w)\ne x$, then
--   $$\lim_{\varepsilon\to0^+}\frac{P_\varepsilon}{2\varepsilon}=q_1+q_2.\tag{23}$$
--
--   In words, $P_\varepsilon/(2\varepsilon)$ is the conditional density of $X$ at $x$ given $W$, and it is the sum of the two root contributions $f_d(r_\ell)/|g'(r_\ell)|$. The lemma is the pointwise step behind the importance-sampling representation of Theorem 4.
--
--   **Formalization Note** $P_\varepsilon$ is the standard Gaussian measure of $\{z:|X(w,z)-x|\le\varepsilon\}$ (`Peps`), and $q_1,q_2$ are `DeltaGamma.q1`, `q2` of the supplement's model. The limit is taken along $\varepsilon>0$.
--
--   Differences from the source:
--   - correction: lim_{ε→0} P_ε/(2ε) = q1 + q2 w.p.1 → the limit holds at every w with g*(w) ≠ x; reason: at g*(w) = x, P_ε is of order √ε, so P_ε/(2ε) → ∞ while q1 + q2 = 0; the printed w.p.1 claim fails when Pr{g* = x} > 0 (counterexample: δ1j = γ1j = 0 for all j < d, so g* is the constant c1 − δ1d²/(4γ1d), and x equal to it). The proof on p. 16 discards {g* = x} as a probability-zero event. Only the points with g*(w) = x are excluded, and the Lean statement gives the w.p.1 form whenever Pr{g* = x} = 0
--   - encoding: ε → 0 → ε → 0⁺ (the filter 𝓝[>] 0); reason: ε is the half-width of the window {|X − x| ≤ ε} and is positive throughout §4.2.1
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, pp. 15–16, Lemma 5, Equation (23); proof p. 16

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Lemma 5, pp. 15–16, Equation (23): for `γ_{1d} > 0`, at every value `w` of `(Z_1, …, Z_{d-1})`
with `g*(w) ≠ x`, `P_ε / (2ε) → q₁ + q₂` as `ε → 0⁺`. -/
theorem lemma_5 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d) (x : ℝ) (w : Fin d' → ℝ)
    (hw : M.gStar w ≠ x) :
    Tendsto (fun ε => Peps M x w ε / (2 * ε)) (𝓝[>] 0) (𝓝 (M.q1 w x + M.q2 w x)) := by sorry

end CoVaRMC.Batching.Supplement
