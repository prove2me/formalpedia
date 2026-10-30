-- Prove2me | Theorems.Thm_FastRegretAudit_Individual_corollary_12
-- name    : FastRegretAudit.Individual.corollary_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:10.823754+00:00
-- url     : https://prove2.me/theorems/30d86c63-6cf8-469a-b188-a0374a240a67
-- title:
--   Corollary 12 — individual OFTRL regret at the exact horizon stepsize
-- statement:
--   Consider $n\ge2$ players, each with $d\ge1$ pure strategies, and fixed payoffs $u_i:\prod_{j<n}S_j\to[0,1]$. At each round players randomize independently with mixed profile $w^t$. The feedback vector to player $i$ is
--
--   $$u^t_{i,x}=\sum_{s_{-i}}\left(\prod_{j\ne i}w^t_{j,s_j}\right)u_i(x,s_{-i}).$$
--
--   Each real-valued regularizer $\mathcal R_i$ satisfies exactly the paper's midpoint 1-strong-convexity condition for $\|\cdot\|_1$ on its simplex. Set
--
--   $$R=\max_{i<n}\left(\sup_{f\in\Delta(S_i)}\mathcal R_i(f)-\inf_{f\in\Delta(S_i)}\mathcal R_i(f)\right),\qquad\eta=(n-1)^{-1/2}T^{-1/4}.$$
--
--   For any integer horizon $T\ge1$ and every attaining joint OFTRL prefix through $T$, initialized by regularizer minimization and using $M_i^t=u_i^{t-1}$ with this fixed stepsize, every player $i$ and every fixed mixed comparator $w_i^*\in\Delta(S_i)$ satisfy
--
--   $$\sum_{t=1}^T\langle w_i^*-w_i^t,u_i^t\rangle\le(R+4)\sqrt{n-1}\,T^{1/4}.$$
--
--   Since the bound holds for every comparator, it bounds cumulative external regret. Different players may have different regularizers. No zero-sum, equilibrium, welfare, or smooth-game condition is needed.
--
--   **Formalization Note** Initial feedback is the same expected utility evaluated at $w^0$. The range is computed exactly in $\mathrm{EReal}$, including $+\infty$; the displayed finite formula is unchanged when the range is finite. The singleton simplex and zero range are allowed. The only run hypothesis is the global OFTRL optimality relation; RVU, leaders, and stability are not hypotheses.
--
--   Differences from the source:
--   - encoding: finite nonempty strategy spaces and negative-power stepsize → Fin n and Fin d with n ≥ 2, d > 0 and T ≥ 1; reason: finite relabelling and exclusion only of undefined negative-power cases
--   - encoding: argmin and argmax updates at the rounds used by the result → global optimality inequalities on the required finite prefixes; reason: expresses every attaining run without assuming unused future optimizers exist
--   - encoding: R is the exact supremum minus infimum with no separate finiteness assumption → EReal exact range and a bound in EReal with the other finite terms embedded; reason: agrees with the real formula for finite range and retains the infinite-range case without default real extrema
--   - reading: the first predictor uses an unspecified initial utility vector → initial utility is the feedback evaluated at the initial game profile; reason: the consecutive-profile variation estimate in Theorem 11 then also covers the first move
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, main p. 5, §3.2, Corollary 12, PDF p. 5; §2, main p. 2; footnotes 2–3, main p. 4

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Definitions.Def_FastRegretAudit_Individual_Runs
import Definitions.Def_FastRegretAudit_Individual_Geometry
import Definitions.Def_FastRegretAudit_Individual_Range

namespace FastRegretAudit.Individual

/-- Corollary 12, main p. 5 (PDF 5), with the exact prescribed stepsize
and range. Reading: initial feedback is evaluated at the initial game profile.
The only algorithm hypothesis is the actual global OFTRL optimality relation. -/
theorem corollary_12 {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ)
    (h𝓡 : ∀ i, IsMidpointStronglyConvex RegLearnGames.TotalRegret.l1 (𝓡 i))
    (T : ℕ) (hT : 1 ≤ T) (w : ℕ → Fin n → Fin d → ℝ)
    (hw : IsGameOFTRLThrough u 𝓡 (corollaryStepsize n T) w T) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ((∑ t ∈ Finset.Icc 1 T,
        (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i : ℝ) : EReal) ≤
        (commonRange 𝓡 + 4) *
          ((Real.sqrt ((n : ℝ) - 1) * Real.rpow (T : ℝ) (1 / 4 : ℝ) : ℝ) : EReal) := by sorry

end FastRegretAudit.Individual
