-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_12
-- name    : DPCutRelease.Main.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:39.47821+00:00
-- url     : https://prove2.me/theorems/9f9780bc-9290-4fd0-b98f-e4bb072e8307
-- title:
--   Lemma 12 — clipping: Y is ε₀-DP and Y + w′ is within (γ/2)·w(S) on every cut w.p. 1 − β₀
-- statement:
--   Fix $\varepsilon_0,\beta_0,\gamma\in(0,1)$ and $n$. For a nonnegative weight vector $w$ let $U=\frac8{\varepsilon_0\gamma}\log\frac n{\beta_0}$, $V=\frac2{\varepsilon_0}\log\frac n{\beta_0}$, and decompose $w=w'+v$ with (Eq. (5))
--   $$v_e=(w_e-U)_+,\qquad w'_e=\min\{w_e,U\},$$
--   and release (Eq. (6)) $Y_e=\max\{0,\ v_e+L_e-V\}$ with $L_e\sim\mathrm{Lap}(1/\varepsilon_0)$ independent. Then releasing $Y$ is $\varepsilon_0$-edge-DP, i.e. $(\varepsilon_0,0)$ edge-DP, and with probability at least $1-\beta_0$, for every cut $S\subseteq[n]$,
--   $$\big|Y(S,V\setminus S)+w'(S,V\setminus S)-w(S,V\setminus S)\big|\le\frac\gamma2\,w(S,V\setminus S).$$
--   It is the preprocessing step that lets the main algorithm assume bounded weights.
--
--   **Formalization Note.** `clipY`, `clipW` (Algorithms module); $L_e=\omega_2[u,v]/\varepsilon_0$ with $\omega\sim$ `noiseLaw`.
--
--   Differences from the source:
--   - reading: "releasing Y is ε₀-DP" → IsEdgeDPFun noiseLaw clipY ε₀ 0; reason: ε-DP is (ε, 0)-DP
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 18, Lemma 12 (Eqs. (5)–(6), p. 18)

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 12 (p. 18): for `ε₀, β₀, γ ∈ (0, 1)`, releasing `Y` of Eq. (6) is `ε₀`-DP, and for every
nonnegative `w`, with probability at least `1 − β₀`, every cut has
`|Y(S) + w'(S) − w(S)| ≤ (γ/2) w(S)` (`w'` of Eq. (5)). -/
theorem lemma_12 (n : ℕ) (ε0 β0 γ : ℝ) (hε0 : 0 < ε0) (hε0' : ε0 < 1) (hβ0 : 0 < β0)
    (hβ0' : β0 < 1) (hγ : 0 < γ) (hγ' : γ < 1) :
    IsEdgeDPFun noiseLaw (fun (w : EdgeVec n) ω => clipY γ ε0 β0 w ω) ε0 0 ∧
      ∀ w : EdgeVec n, Nonneg w →
        noiseLaw {ω | ∃ S : Finset (Fin n), γ / 2 * cutValue w S <
            |cutValue (clipY γ ε0 β0 w ω) S + cutValue (clipW γ ε0 β0 w) S - cutValue w S|}
          ≤ ENNReal.ofReal β0 := by sorry

end DPCutRelease.Main
