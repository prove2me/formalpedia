-- Prove2me | Theorems.Thm_DelayedGamesMAO_theorem_2_3
-- name    : DelayedGamesMAO.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:08.495213+00:00
-- url     : https://prove2.me/theorems/61b6f1cb-3bee-4988-9f75-b749c02b9cea
-- title:
--   Theorems 2 and 3 — MAO-OMD: $O(q_{\max})$ regret in self-play and $O(\sqrt{T+d_{\mathrm{tot}}})$ against any opponent
-- statement:
--   Let $X$ and $Y$ be nonempty compact convex subsets of finite-dimensional real normed spaces, and let $f:X\times Y\to\mathbb R$ be differentiable, convex in its first argument and concave in its second, with loss gradients $g^x=\nabla_xf$ and $g^y=-\nabla_yf$ satisfying Assumption 1 with constants $G,L>0$. Let $T\ge1$ and let $(d_t)$ be delays with $t+d_t\le T$, unknown to the players. Write
--   $$
--   \mathrm{Reg}^x_T(u)=\sum_{t=1}^T\bigl(f(x_t,y_t)-f(u,y_t)\bigr),\qquad \mathrm{Reg}^y_T(v)=\sum_{t=1}^T\bigl(f(x_t,v)-f(x_t,y_t)\bigr),
--   $$
--   and $\bar x_T=\frac1T\sum_{t=1}^Tx_t$, $\bar y_T=\frac1T\sum_{t=1}^Ty_t$.
--
--   1. **(Self-play, Theorem 2.)** Let $\psi_x$ on $X$ and $\psi_y$ on $Y$ satisfy Assumption 2 with the same constant $M$. If $(x_t)$ is a run of MAO-OMD on the gradients $g^x(x_t,y_t)$ and $(y_t)$ a run of MAO-OMD on the gradients $g^y(x_t,y_t)$, both under the delays $(d_t)$, then for all $u\in X$, $v\in Y$:
--   $$
--   \mathrm{Reg}^x_T(u)\le(16G\sqrt M+48LM)\,q_{\max},\qquad \mathrm{Reg}^y_T(v)\le(16G\sqrt M+48LM)\,q_{\max},
--   $$
--   $$
--   \mathrm{Reg}^x_T(u)+\mathrm{Reg}^y_T(v)\le(16G\sqrt M+32LM)\,q_{\max},\qquad f(\bar x_T,v)-f(u,\bar y_T)\le\frac{(16G\sqrt M+32LM)\,q_{\max}}T .
--   $$
--   Hence the individual regrets, the social regret and $T$ times the duality gap are all $O((G\sqrt M+LM)q_{\max})$.
--
--   2. **(Arbitrary opponent, Theorem 3.)** Let $\psi_x$ on $X$ satisfy Assumption 2 with a constant $M$. For every sequence $y_t\in Y$ of opponent actions, if $(x_t)$ is a run of MAO-OMD on the gradients $g^x(x_t,y_t)$, then for every $u\in X$,
--   $$
--   \mathrm{Reg}^x_T(u)\le12\sqrt2\,G\sqrt{M(T+d_{\mathrm{tot}})}+8LM\,q_{\max}.
--   $$
--
--   One algorithm, run without knowing the delays or the opponent, gets regret $O(q_{\max})=O(\sigma_{\max}+1)$ when the opponent also runs it and the minimax delayed rate $O(\sqrt{T+d_{\mathrm{tot}}})$ against anyone. Both rates are optimal.
--
--   **Formalization Note** MAO-OMD is Algorithm 1 with the congestion schedule (10), the tuning (9) and $\gamma=\max\{4L,2G/\sqrt M\}$. The constants are those derived in the printed proofs (p.6). Each supremum over comparators is stated as a bound for every comparator, and the averages are the published `ModernOnlineLearning.SaddlePoint.avg`.
--
--   Differences from the source:
--   - reading: O((G√M + LM)q_max), O((G√M + LM)q_max/T) and O(G√(M(T + d_tot)) + LMq_max) → the explicit bounds of the printed proofs: (16G√M + 48LM)q_max, (16G√M + 32LM)q_max, (16G√M + 32LM)q_max/T, 12√2·G√(M(T + d_tot)) + 8LMq_max; reason: the O(·) hide only absolute constants (G, L, M are explicit), so these bounds imply the printed statements
--   - encoding: Reg_T^x = sup_u, Reg_T^y = sup_v, SocReg_T = Reg_T^x + Reg_T^y, DualGap_T = sup_v f(x̄_T, v) − inf_u f(u, ȳ_T) → a bound for every comparator u ∈ X, v ∈ Y (∀-form); reason: a supremum is at most B iff every term is; all quantities are finite here; same content
--   - encoding: Theorems 2 and 3, two statements → one theorem with a self-play clause and an opponent clause; reason: the two statements jointly; same content
--   - generalization: f differentiable on X × Y with g^x = ∇_x f, g^y = −∇_y f → derivative fields of f(·, y) within X and of f(x, ·) within Y on X × Y (IsConvexConcaveGame); reason: the partial gradients of a differentiable f are such fields, so the statement specializes to the paper's; it asks nothing of f off X × Y
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - encoding: the run of MAO-OMD with learning rates following (9) → a pair (x, η) with IsMAOOMDRun (Algorithm 1 with (10), (9), γ = max{4L, 2G/√M}); reason: (9) determines η; the arg min is relational; same instances
--   - encoding: an opponent y taking arbitrary, possibly adaptive actions → every sequence y_t ∈ Y for t ∈ [T]; reason: the bound is about realized sequences; same instances
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, Theorem 2, p.5 (proof pp.5–6) and Theorem 3, p.6 (proof p.6); constants from the proofs, p.6

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting
import Definitions.Def_DelayedGamesMAO_IsConvexConcaveGame
import Definitions.Def_DelayedGamesMAO_Assumption1
import Definitions.Def_DelayedGamesMAO_Assumption2
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_dtot
import Definitions.Def_DelayedGamesMAO_IsMAOOMDRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Theorems 2 and 3 (best of both worlds for MAO-OMD in smooth convex–concave zero-sum games).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, Theorem 2, p.5 (proof pp.5–6) and Theorem 3, p.6 (proof p.6).

Theorem 2: "Let Assumption 1 hold. If both players run MAO-OMD with regularizers satisfying
Assumption 2 under arbitrary unknown delays, then the social regret `SocReg_T` and individual
regrets `Reg_T^x, Reg_T^y` are all `O((G√M + LM)q_max)`, while `DualGap_T` is
`O((G√M + LM)q_max / T)`." Its proof gives `SocReg_T ≤ (16G√M + 32LM)q_max`,
`DualGap_T ≤ (16G√M + 32LM)q_max/T` and `Reg_T^p ≤ (16G√M + 48LM)q_max`; both regularizers satisfy
Assumption 2 "with the same constant `M`" (p.5).

Theorem 3: "Let Assumption 1 hold. If player x runs MAO-OMD with a regularizer satisfying
Assumption 2 under arbitrary unknown delays and against an opponent y taking arbitrary actions,
then its individual regret `Reg_T^x` is `O(G√(M(T + d_tot)) + LMq_max)`." Its proof gives
`Reg_T^x ≤ (8LM + 4G√M)q_max + 8G√(M(T + 2d_tot))`, and with `q_max ≤ √(T + 2d_tot)` and
`T + 2d_tot ≤ 2(T + d_tot)` the explicit bound `12√2·G√(M(T + d_tot)) + 8LMq_max`.

Regrets (p.3): `Reg_T^x = sup_{x∈X} ∑_t (f(x_t, y_t) − f(x, y_t))`,
`Reg_T^y = sup_{y∈Y} ∑_t (f(x_t, y) − f(x_t, y_t))`, `SocReg_T = Reg_T^x + Reg_T^y`,
`DualGap_T = sup_{y∈Y} f(x̄_T, y) − inf_{x∈X} f(x, ȳ_T)` with `x̄_T = (1/T)∑_t x_t`.

**Formalization Note.** `X, Y` are nonempty compact convex subsets of finite-dimensional real
normed spaces; `f` is convex–concave with loss-gradient maps `gx = ∇_x f`, `gy = −∇_y f`
(`IsConvexConcaveGame`) satisfying Assumption 1. Player x's run is MAO-OMD
(`IsMAOOMDRun`: Algorithm 1 with (10), (9), `γ = max{4L, 2G/√M}`) on its gradients
`gx(x_t, y_t)`, player y's on `gy(x_t, y_t)`, both under the same delays `d` with
`t + d_t ≤ T` (p.3). The `O(·)` bounds are stated with the explicit constants of the printed
proofs. Each supremum is stated in its `∀`-form (`sup ≤ B` iff every term is `≤ B`), and the
averages are `ModernOnlineLearning.SaddlePoint.avg T` (`(1/T)∑_{t=1}^T`). In the opponent clause
`y_t ∈ Y` is arbitrary (it may depend on the history; the bound is for every realized
sequence). -/
theorem theorem_2_3 {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (f : EX → EY → ℝ) (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (hgame : IsConvexConcaveGame X Y f gx gy) (G L : ℝ) (hA1 : Assumption1 X Y gx gy G L) :
    -- Theorem 2: both players run MAO-OMD (self-play)
    (∀ (M : ℝ) (ψx : EX → ℝ) (dψx : EX → EX →L[ℝ] ℝ) (w0x : EX)
        (ψy : EY → ℝ) (dψy : EY → EY →L[ℝ] ℝ) (w0y : EY),
      Assumption2 X ψx dψx w0x M → Assumption2 Y ψy dψy w0y M →
      ∀ (T : ℕ), 1 ≤ T → ∀ d : ℕ → ℕ, (∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) →
      ∀ (x : ℕ → EX) (y : ℕ → EY) (ηx ηy : ℕ → ℝ),
        IsMAOOMDRun X ψx dψx w0x M L G T d (fun t => gx (x t) (y t)) x ηx →
        IsMAOOMDRun Y ψy dψy w0y M L G T d (fun t => gy (x t) (y t)) y ηy →
        (∀ u ∈ X, ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) ≤
            (16 * G * Real.sqrt M + 48 * L * M) * (qmax d T : ℝ)) ∧
        (∀ v ∈ Y, ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
            (16 * G * Real.sqrt M + 48 * L * M) * (qmax d T : ℝ)) ∧
        (∀ u ∈ X, ∀ v ∈ Y,
          ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) +
              ∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t)) ≤
            (16 * G * Real.sqrt M + 32 * L * M) * (qmax d T : ℝ)) ∧
        (∀ u ∈ X, ∀ v ∈ Y,
          f (ModernOnlineLearning.SaddlePoint.avg T x) v -
              f u (ModernOnlineLearning.SaddlePoint.avg T y) ≤
            (16 * G * Real.sqrt M + 32 * L * M) * (qmax d T : ℝ) / (T : ℝ))) ∧
    -- Theorem 3: player x runs MAO-OMD against an arbitrary opponent
    (∀ (M : ℝ) (ψx : EX → ℝ) (dψx : EX → EX →L[ℝ] ℝ) (w0x : EX),
      Assumption2 X ψx dψx w0x M →
      ∀ (T : ℕ), 1 ≤ T → ∀ d : ℕ → ℕ, (∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) →
      ∀ (y : ℕ → EY), (∀ t ∈ Finset.Icc 1 T, y t ∈ Y) →
      ∀ (x : ℕ → EX) (ηx : ℕ → ℝ),
        IsMAOOMDRun X ψx dψx w0x M L G T d (fun t => gx (x t) (y t)) x ηx →
        ∀ u ∈ X, ∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t)) ≤
          12 * Real.sqrt 2 * G * Real.sqrt (M * ((T : ℝ) + (dtot d T : ℝ))) +
            8 * L * M * (qmax d T : ℝ)) := by sorry

end DelayedGamesMAO
