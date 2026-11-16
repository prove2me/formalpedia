-- Prove2me | Theorems.Thm_DelayedGamesMAO_Supplement_theorem_4
-- name    : DelayedGamesMAO.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:54:31.946894+00:00
-- url     : https://prove2.me/theorems/632c7c0b-fda9-4eec-9a49-b0cd738dd2a1
-- title:
--   Theorem 4, p.7 — refined BOLD: $C_B\sqrt{(T+d_{tot})(1+\log q_{\max})}$ regret, and $O((LM+G\sqrt M)q_{\max})$ in self-play
-- statement:
--   This is Theorem 4, the guarantee of the **refined BOLD reduction**. The reduction runs independent copies of an undelayed online learner $B$ and plays round $t$ with the copy of index $i_t$, the smallest copy that holds no pending round (Algorithm 2). Write $n_k$ for the number of rounds in $[T]$ given to copy $k$, $d_{tot}=\sum_{t\in[T]}d_t$ for the total delay and $q_{\max}=\max_{t\in[T]}(|P_t|+1)$ for the largest number of active rounds, where feedback of round $t$ arrives at the end of round $t+d_t\le T$.
--
--   1. **Arbitrary losses.** Let $W$ be a nonempty compact convex domain, let the losses $f_t$ with gradients $g_t=\nabla f_t(w_t)$ come from a class $\mathcal L$, and suppose every undelayed run of $B$ on $n\ge1$ rounds of losses from $\mathcal L$ has regret at most $C_B\sqrt n$ against every comparator in $W$. Then every run of the reduction satisfies, for every $u\in W$,
--   $$
--   \sum_{t=1}^T\big(f_t(w_t)-f_t(u)\big)\;\le\;C_B\sum_k\sqrt{n_k}\;\le\;C_B\sqrt{(T+d_{tot})(1+\log q_{\max})}.
--   $$
--
--   2. **Self-play in a smooth game.** Let $f$ be a differentiable convex–concave function on nonempty compact convex domains $X\times Y$ with loss gradients $g^x=\nabla_xf$, $g^y=-\nabla_yf$ satisfying Assumption 1 (constants $G,L$), and let $M$ be a Bregman radius of Assumption 2 for both domains. Let $B^x$ on $X$ and $B^y$ on $Y$ be base learners such that, for some constant $C$ and every horizon $n\ge1$, their undelayed self-play in $f$ has both individual regrets and the social regret at most $C(LM+G\sqrt M)$. If both players use the reduction with the same delays, then
--   $$
--   \mathrm{Reg}^x_T,\ \mathrm{Reg}^y_T,\ \mathrm{SocReg}_T\;\le\;C\,(LM+G\sqrt M)\,q_{\max}.
--   $$
--
--   Part 1 shows that the smallest-idle-index rule loses only a factor $\sqrt{1+\log q_{\max}}$ against the minimax rate $\sqrt{T+d_{tot}}$; part 2 shows that it keeps the fast $O(q_{\max})$ rate in self-play. Neither part needs advance knowledge of the delays: the indices depend only on which feedback has arrived.
--
--   **Formalization Note** The base learner is a deterministic map from the list of gradients fed so far to its next action. Regrets are stated against every comparator (the supremum form). The sum over $k$ runs over the instance indices actually used. In part 2 the $O(\cdot)$ hypothesis and conclusion share the explicit constant $C$.
--
--   Differences from the source:
--   - generalization: losses from the online convex setting of Section 2 (differentiable convex f_t on W with g_t = ∇f_t(w_t)) → an arbitrary class 𝓛 of (loss, gradient field) pairs, the same class in the hypothesis on B and in the conclusion; reason: taking 𝓛 to be the §2 losses (with whatever restriction B's guarantee is stated for) gives the source's claim
--   - encoding: W ⊆ ℝ^n with a norm and its dual norm; gradients in the dual → W a nonempty compact convex subset of a finite-dimensional real normed space; gradients E →L[ℝ] ℝ; reason: the convention of the published mission; same instances
--   - encoding: B guarantees regret at most C_B√n for every n ≥ 1 (adaptive environment) → B a deterministic map from gradient lists to actions in W; for every n ≥ 1, every loss sequence in 𝓛 and every comparator, the n-round regret of its undelayed run is ≤ C_B√n; reason: a deterministic learner facing an adaptive environment produces a fixed realized sequence
--   - reading: B guarantees individual and social regret O(LM + G√M) for every horizon ⇒ SocReg_T, Reg^p_T = O((LM + G√M)q_max) → for every constant C: if all three regrets of every undelayed n-round self-play of (Bx, By) in the game f are ≤ C(LM + G√M), then all three regrets of the reduction are ≤ C(LM + G√M)q_max; reason: the proof (p.34) sums at most q_max pair bounds with the same constant; this implies the O-statement
--   - encoding: one base learner B for both players → base learners Bx on X and By on Y; reason: the players' domains differ
--   - encoding: Reg_T = sup_u Reg_T(u); Reg^x_T, Reg^y_T, SocReg_T as suprema → the ∀-forms over comparators; reason: sup ≤ b iff every term ≤ b
--   - encoding: ∑_k over the instances → sum over the indices used, (Finset.Icc 1 T).image (boldIndex d); reason: these are exactly the instances created
--   - encoding: feedback after round T does not matter (p.3, footnote 1) → hypothesis t + d_t ≤ T for t ∈ [T]; reason: the paper's standing convention, as in the published goal
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §4, Theorem 4, p.7; Algorithm 2 and proofs in App. B.1–B.3, pp.33–34

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsConvexConcaveGame
import Definitions.Def_DelayedGamesMAO_Assumption1
import Definitions.Def_DelayedGamesMAO_Assumption2
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_dtot
import Definitions.Def_DelayedGamesMAO_Supplement_boldIndex
import Definitions.Def_DelayedGamesMAO_Supplement_boldLoad
import Definitions.Def_DelayedGamesMAO_Supplement_IsBoldRun
import Definitions.Def_DelayedGamesMAO_Supplement_IsUndelayedRun

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **Theorem 4 (guarantees of the refined BOLD reduction).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §4, Theorem 4, p.7 (proofs App. B.2–B.3, pp.33–34):
"The refined BOLD reduction in Algorithm 2 has the following guarantees without advance knowledge
of the delays: (i) In the online convex setting of Section 2, if `B` guarantees regret at most
`C_B√n` for every `n ≥ 1`, then `Reg_T ≤ C_B ∑_k √n_k ≤ C_B √((T + d_tot)(1 + log q_max))`.
(ii) Under Assumptions 1 and 2, if `B` guarantees individual and social regret `O(LM + G√M)` in
undelayed zero-sum self-play for every horizon, then both players using the reduction with common
delays satisfy `SocReg_T, Reg^p_T = O((LM + G√M)q_max)` for `p ∈ {x, y}`."

**Formalization Note.** `B : List (E →L[ℝ] ℝ) → E` is a deterministic undelayed learner with
values in the domain; "without advance knowledge of the delays" is a property of the
construction (`boldIndex` depends on the pending sets only), not a hypothesis. In (i) the losses
come from an arbitrary class `𝓛` of (loss, gradient field) pairs, the same in the hypothesis on
`B` and in the conclusion; the gradient of round `t` is `g_t = gl t (w t)`. Regrets are stated
in their `∀`-forms over comparators. `∑_k` runs over the instances created,
`(Finset.Icc 1 T).image (boldIndex d)`; `log` is `Real.log`. In (ii) `O(LM + G√M)` in the
hypothesis is `≤ C·(LM + G√M)` for every horizon `n ≥ 1` with a constant `C`, and the conclusion
is `≤ C·(LM + G√M)·q_max` with the same `C`; the base learners are `Bx` on `X` and `By` on `Y`,
both players use the same delays `d`, and the hypothesis is about their undelayed self-play in
the same game `f`. Rounds are `1, …, T` with `t + d_t ≤ T` (p.3, footnote 1). -/
theorem theorem_4 {E EX EY : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY] :
    -- (i) online convex setting, arbitrary (adaptive) losses
    (∀ (W : Set E), W.Nonempty → IsCompact W → Convex ℝ W →
      ∀ (𝓛 : Set ((E → ℝ) × (E → E →L[ℝ] ℝ))) (B : List (E →L[ℝ] ℝ) → E),
      (∀ ℓ, B ℓ ∈ W) → ∀ CB : ℝ,
      (∀ n : ℕ, 1 ≤ n → ∀ (fl : ℕ → E → ℝ) (gl : ℕ → E → E →L[ℝ] ℝ) (v : ℕ → E),
        (∀ j ∈ Finset.Icc 1 n, (fl j, gl j) ∈ 𝓛) →
        IsUndelayedRun B (fun j => gl j (v j)) n v →
        ∀ u ∈ W, ∑ j ∈ Finset.Icc 1 n, (fl j (v j) - fl j u) ≤ CB * Real.sqrt (n : ℝ)) →
      ∀ (T : ℕ), 1 ≤ T → ∀ d : ℕ → ℕ, (∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) →
      ∀ (fl : ℕ → E → ℝ) (gl : ℕ → E → E →L[ℝ] ℝ) (w : ℕ → E),
        (∀ t ∈ Finset.Icc 1 T, (fl t, gl t) ∈ 𝓛) →
        IsBoldRun B d (fun t => gl t (w t)) T w →
        (∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, (fl t (w t) - fl t u) ≤
            CB * ∑ k ∈ (Finset.Icc 1 T).image (boldIndex d), Real.sqrt (boldLoad d T k : ℝ)) ∧
        CB * ∑ k ∈ (Finset.Icc 1 T).image (boldIndex d), Real.sqrt (boldLoad d T k : ℝ) ≤
          CB * Real.sqrt (((T : ℝ) + (dtot d T : ℝ)) * (1 + Real.log (qmax d T : ℝ)))) ∧
    -- (ii) both players use the reduction with common delays in a smooth zero-sum game
    (∀ (X : Set EX) (Y : Set EY), X.Nonempty → IsCompact X → Convex ℝ X →
      Y.Nonempty → IsCompact Y → Convex ℝ Y →
      ∀ (f : EX → EY → ℝ) (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ),
      IsConvexConcaveGame X Y f gx gy → ∀ (G L : ℝ), Assumption1 X Y gx gy G L →
      ∀ (M : ℝ) (ψx : EX → ℝ) (dψx : EX → EX →L[ℝ] ℝ) (w0x : EX)
        (ψy : EY → ℝ) (dψy : EY → EY →L[ℝ] ℝ) (w0y : EY),
      Assumption2 X ψx dψx w0x M → Assumption2 Y ψy dψy w0y M →
      ∀ (Bx : List (EX →L[ℝ] ℝ) → EX) (By : List (EY →L[ℝ] ℝ) → EY),
      (∀ ℓ, Bx ℓ ∈ X) → (∀ ℓ, By ℓ ∈ Y) → ∀ C : ℝ,
      (∀ n : ℕ, 1 ≤ n → ∀ (xs : ℕ → EX) (ys : ℕ → EY),
        IsUndelayedRun Bx (fun j => gx (xs j) (ys j)) n xs →
        IsUndelayedRun By (fun j => gy (xs j) (ys j)) n ys →
        (∀ u ∈ X, ∑ j ∈ Finset.Icc 1 n, (f (xs j) (ys j) - f u (ys j)) ≤
            C * (L * M + G * Real.sqrt M)) ∧
        (∀ v ∈ Y, ∑ j ∈ Finset.Icc 1 n, (f (xs j) v - f (xs j) (ys j)) ≤
            C * (L * M + G * Real.sqrt M)) ∧
        (∀ u ∈ X, ∀ v ∈ Y,
          ∑ j ∈ Finset.Icc 1 n, (f (xs j) (ys j) - f u (ys j)) +
              ∑ j ∈ Finset.Icc 1 n, (f (xs j) v - f (xs j) (ys j)) ≤
            C * (L * M + G * Real.sqrt M))) →
      ∀ (T : ℕ), 1 ≤ T → ∀ d : ℕ → ℕ, (∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) →
      ∀ (x : ℕ → EX) (y : ℕ → EY),
        IsBoldRun Bx d (fun t => gx (x t) (y t)) T x →
        IsBoldRun By d (fun t => gy (x t) (y t)) T y →
        (∀ u ∈ X, ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) ≤
            C * (L * M + G * Real.sqrt M) * (qmax d T : ℝ)) ∧
        (∀ v ∈ Y, ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
            C * (L * M + G * Real.sqrt M) * (qmax d T : ℝ)) ∧
        (∀ u ∈ X, ∀ v ∈ Y,
          ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) +
              ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
            C * (L * M + G * Real.sqrt M) * (qmax d T : ℝ))) := by sorry

end DelayedGamesMAO.Supplement
