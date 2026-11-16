-- Prove2me | Theorems.Thm_DelayedGamesMAO_Supplement_theorem_7
-- name    : DelayedGamesMAO.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:56:11.509665+00:00
-- url     : https://prove2.me/theorems/7c731156-d0f2-401f-b35d-0985baaa7d5f
-- title:
--   Theorem 7, p.26 — player-dependent delays: regrets $O((G\sqrt M+LM)(\sigma^x_{\max}+\sigma^y_{\max}+1))$
-- statement:
--   This is Theorem 7, on **player-dependent delays**. In a two-player zero-sum game the gradient $g^x_t$ of round $t$ reaches player $x$ at the end of round $t+d^x_t$, and $g^y_t$ reaches player $y$ at the end of round $t+d^y_t$. For each player $p$ let $P^p_t=\{s\in[t-1]: s+d^p_s\ge t\}$ and $\sigma^p_{\max}=\max_{t\in[T]}|P^p_t|$. The players announce which feedback they have received, so both know the **effective delays** $\tilde d_t=\max\{d^x_t,d^y_t\}$ and both run MAO-OMD (Algorithm 1 with $\gamma=\max\{4L,2G/\sqrt M\}$) under $\tilde d$.
--
--   Let $f$ be a differentiable convex–concave function on nonempty compact convex domains $X\times Y$ whose loss gradients satisfy Assumption 1 with constants $G,L$, and let both regularizers satisfy Assumption 2 with the same $M$. Then, for every horizon $T\ge1$ and all delays with $t+d^p_t\le T$,
--   $$
--   \mathrm{SocReg}_T\le(16G\sqrt M+32LM)(\sigma^x_{\max}+\sigma^y_{\max}+1),\qquad
--   \mathrm{Reg}^x_T,\ \mathrm{Reg}^y_T\le(16G\sqrt M+48LM)(\sigma^x_{\max}+\sigma^y_{\max}+1).
--   $$
--
--   The fast self-play rates of Theorem 2 thus survive player-dependent delays, with the maximal number of pending rounds of either player in place of $q_{\max}$.
--
--   **Formalization Note** Each player's run is the published MAO-OMD run under the delay sequence $\tilde d$, with gradients $g^x(x_t,y_t)$ and $g^y(x_t,y_t)$. Regrets are stated against every comparator (the supremum form). The constants are those of Theorem 2's proof, through which the source proves Theorem 7.
--
--   Differences from the source:
--   - reading: SocReg_T, Reg^x_T, Reg^y_T are O((G√M + LM)(σ^x_max + σ^y_max + 1)) → SocReg_T ≤ (16G√M + 32LM)(σ^x_max + σ^y_max + 1) and Reg^x_T, Reg^y_T ≤ (16G√M + 48LM)(σ^x_max + σ^y_max + 1); reason: the proof applies Theorem 2, whose proof gives these constants (as in the published goal); explicit constants imply the O-statement
--   - encoding: each player stores its gradient of round s until the end of round s + d̃_s and then passes it to MAO-OMD → each player's actions form an IsMAOOMDRun under the delay sequence d̃_t = max{d^x_t, d^y_t}; reason: the paper states that this is Algorithm 1 run unchanged under d̃ (p.26)
--   - encoding: suprema in Reg^x_T, Reg^y_T, SocReg_T → ∀-forms over comparators; reason: sup ≤ b iff every term ≤ b
--   - encoding: feedback after round T does not matter (p.3, footnote 1) → hypotheses t + d^x_t ≤ T and t + d^y_t ≤ T for t ∈ [T]; reason: the paper's standing convention, for both players
--   - encoding: X ⊆ ℝ^{n_x}, Y ⊆ ℝ^{n_y} with norms → nonempty compact convex subsets of finite-dimensional real normed spaces; reason: the convention of the published mission; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §8, Theorem 7, p.26 (setting p.25)

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsConvexConcaveGame
import Definitions.Def_DelayedGamesMAO_Assumption1
import Definitions.Def_DelayedGamesMAO_Assumption2
import Definitions.Def_DelayedGamesMAO_sigmaMax
import Definitions.Def_DelayedGamesMAO_IsMAOOMDRun

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **Theorem 7 (player-dependent delays).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §8, Theorem 7, p.26 (setting p.25, proof p.26): "Let Assumptions 1 and 2
hold. Under player-dependent delays, if both players run MAO-OMD under the effective delays
`d̃_t = max{d^x_t, d^y_t}`, then `SocReg_T`, `Reg^x_T`, and `Reg^y_T` are all
`O((G√M + LM)(σ^x_max + σ^y_max + 1))`."

Setting (p.25): the gradient `g^x_t` of round `t` reaches player x at the end of round
`t + d^x_t`, and `g^y_t` reaches player y at the end of round `t + d^y_t`;
`P^p_t = {s ∈ [t − 1] : s + d^p_s ≥ t}` and `σ^p_max = max_{t∈[T]} |P^p_t|`. Each player stores
its gradient of round `s` until the end of round `s + d̃_s` and only then passes it to MAO-OMD
(Algorithm 1 with `γ = max{4L, 2G/√M}`), p.26.

**Formalization Note.** Each player's run is `DelayedGamesMAO.IsMAOOMDRun` under the delay
sequence `d̃ = fun t => max (dx t) (dy t)` with the gradients `gx(x_t, y_t)`, `gy(x_t, y_t)`, as in
`DelayedGamesMAO.theorem_2_3` with `d` replaced by `d̃`; both regularizers satisfy Assumption 2
with the same `M`. `σ^p_max = sigmaMax d^p T`. The `O(·)` is stated with the explicit constants of
Theorem 2's proof, through which Theorem 7 is proved: `Reg^x_T, Reg^y_T ≤ (16G√M + 48LM)(σ^x_max +
σ^y_max + 1)` and `SocReg_T ≤ (16G√M + 32LM)(σ^x_max + σ^y_max + 1)`. Regrets are in their
`∀`-forms. Rounds are `1, …, T` with `t + d^p_t ≤ T` for both players (p.3, footnote 1). -/
theorem theorem_7 {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (f : EX → EY → ℝ) (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (hgame : IsConvexConcaveGame X Y f gx gy) (G L : ℝ) (hA1 : Assumption1 X Y gx gy G L)
    (M : ℝ) (ψx : EX → ℝ) (dψx : EX → EX →L[ℝ] ℝ) (w0x : EX)
    (ψy : EY → ℝ) (dψy : EY → EY →L[ℝ] ℝ) (w0y : EY)
    (hA2x : Assumption2 X ψx dψx w0x M) (hA2y : Assumption2 Y ψy dψy w0y M)
    (T : ℕ) (hT : 1 ≤ T) (dx dy : ℕ → ℕ)
    (hdx : ∀ t ∈ Finset.Icc 1 T, t + dx t ≤ T) (hdy : ∀ t ∈ Finset.Icc 1 T, t + dy t ≤ T)
    (x : ℕ → EX) (y : ℕ → EY) (ηx ηy : ℕ → ℝ)
    (hx : IsMAOOMDRun X ψx dψx w0x M L G T (fun t => max (dx t) (dy t))
      (fun t => gx (x t) (y t)) x ηx)
    (hy : IsMAOOMDRun Y ψy dψy w0y M L G T (fun t => max (dx t) (dy t))
      (fun t => gy (x t) (y t)) y ηy) :
    (∀ u ∈ X, ∀ v ∈ Y,
      ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) +
          ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
        (16 * G * Real.sqrt M + 32 * L * M) *
          ((sigmaMax dx T : ℝ) + (sigmaMax dy T : ℝ) + 1)) ∧
    (∀ u ∈ X, ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) ≤
        (16 * G * Real.sqrt M + 48 * L * M) *
          ((sigmaMax dx T : ℝ) + (sigmaMax dy T : ℝ) + 1)) ∧
    (∀ v ∈ Y, ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
        (16 * G * Real.sqrt M + 48 * L * M) *
          ((sigmaMax dx T : ℝ) + (sigmaMax dy T : ℝ) + 1)) := by sorry

end DelayedGamesMAO.Supplement
