-- Prove2me | Theorems.Thm_CtxInvOpt_Offline_Supplement_theorem4_projected_cones_regret_false
-- name    : CtxInvOpt.Offline.Supplement.theorem4_projected_cones_regret_false
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:09:15.4203+00:00
-- url     : https://prove2.me/theorems/908f2c64-d1c9-4552-8cf6-e2fbed834847
-- title:
--   Theorem 4 (corrected: refuted, the regret is not O(d⁴ ln T)) — ProjectedCones has regret above K d⁴ ln T for arbitrarily large T, in every d ≥ 2
-- statement:
--   Theorem 4 of the paper claims that **ProjectedCones**, with parameters $\epsilon=d/T$ and $\eta=\epsilon/(2d)$, has worst-case regret $O(d^4\ln T)$ over $T$ periods for every initial knowledge set $C_0$, and runs in polynomial time. The regret claim is false. This item states its refutation.
--
--   Fix a cost dimension $d\ge2$ and an action dimension $n\ge1$. For every constant $K\in\mathbb R$ and every threshold $T_0$ there are a horizon $T\ge T_0$ (with $T\ge1$), a true cost $c^\star$ on the unit sphere $S^d$, compact action sets $X_t\subseteq\mathbb R^n$ that are nonempty with diameter at most $1$, $1$-Lipschitz contexts $f_t:\mathbb R^n\to\mathbb R^d$, and a run of ProjectedCones with
--   $$\epsilon=\frac dT,\qquad \eta=\frac{\epsilon}{2d}$$
--   (actions $x^\pi_t$, expert actions $x^\star_t$ and algorithm states) such that
--   $$K\,d^4\ln T\;<\;\sum_{t=1}^{T}\big(f_t(x^\pi_t)-f_t(x^\star_t)\big)'c^\star .$$
--
--   Here $c^\star\in S^d=C_0$, so the instance is admissible for $C_0=S^d$, the case of no prior knowledge. The constant $K$ and the threshold $T_0$ are arbitrary, and may depend on $d$. The statement therefore contradicts $\mathrm{WCR}^\pi_T(C_0)\le O(d^4\ln T)$ with either absolute or dimension-dependent constants. The recorded counterexample has a $\sqrt T$ lower bound (DISPROOF.md); the Lean statement records the resulting failure of the logarithmic bound.
--
--   The cause is the $p=2$ branch of ConeUpdate, which sets $\widetilde W=W/2+\eta$. Its fixed point $2\eta=1/T$ stays above the low-regret threshold $\epsilon^2=d^2/T^2$ once $T>d^2$, so every later period can be a cone update that turns the proxy cost by about $1/(2\sqrt T)$. An adversary that keeps $c^\star$ off the proxy cost then collects regret of order $\sqrt T$.
--
--   **Formalization Note** Runs are the predicate `IsProjConesRun` of `CtxInvOpt.Offline.Supplement.Run`, with ConeUpdate and PolyCenter as defined in this mission. Regret is the published `cumRegret` over the 0-based periods $t<T$. The run predicate is required in every period, including those after $T$. Any finite run extends by taking zero contexts and the singleton action set $\{0\}$ after $T$; every subsequent effective difference is zero and the state stays fixed. Thus this encoding excludes no finite-horizon witness.
--
--   Differences from the source:
--   - correction: the worst-case regret of ProjectedCones is $O(d^4\ln T)$ → for every $d\ge2$, $n\ge1$, $K$ and $T_0$ some $T\ge T_0$ and some admissible instance and run have regret $>K d^4\ln T$; reason: the printed claim is false (counterexample with $C_0=S^d$, regret $\ge\sqrt T/16$ for $T\ge7$, $T>d^2$; DISPROOF.md, failure of Lemma 8's rate on p. 24)
--   - reading: "Moreover, this algorithm runs in polynomial time in d and T" → not stated; reason: the paper gives no cost model (the cost of the $\psi$ oracle is unspecified), and refuting the regret sentence already refutes the theorem
--   - correction: $\bar\delta=U^{-1}B\delta_{[2:p]}/\|U^{-1}B\delta_{[2:p]}\|$ (Algorithm 1) → $\bar\delta=(U^{-1}B\delta)_{[2:p]}/\|(U^{-1}B\delta)_{[2:p]}\|$; reason: typo, $\delta\in\mathbb R^d$ is first mapped into the $p$ coordinates of $\Delta$, as on p. 23
--   - correction: $q_k=\chi_k/\|\chi\|_2$, $\sum_{k}\gamma_i=1$, $\min_i\hat c'q_k$ (Algorithm 3) → $\|\chi_k\|$, $\sum_k\gamma_k=1$, $\min_k$; reason: index typos
--   - correction: $\bar\delta_t=U_t^{-1}B'_{\Delta_t}\Pi_{\Delta_t}(\delta^\pi_t)$ (p. 23), $\Delta_{t+1}$ spanned by $\tau(t)$ and $\Pi_{\Delta_t}(\delta^\pi_t,p)$ (Algorithm 4) → $U^{-1}B_\Delta\Pi_\Delta\delta^\pi_t$, span of $\tau(t+1)$, $\Pi_\Delta(\delta^\pi_t)$; reason: typos, $B_\Delta$ has $p$ rows and $\tau(t+1)$ is the list just formed
--   - reading: $\eta=\epsilon/2d$ → $\eta=\epsilon/(2d)$; reason: the proof uses $\eta\le\sqrt{\cdot}/(2d)$ (App-18); the counterexample also works for $\eta=(\epsilon/2)d$
--   - reading: after a subspace update, $W=\tan^2(\alpha)I$ with PolyCenter's $\alpha$ (Algorithm 4), while the prose (p. 25) and proof (App-21) use the aperture $\arccos(\eta^{d-1}/d^{3/2})$ → Algorithm 4's $\tan^2\alpha$; reason: the pseudocode is the algorithm's specification; the counterexample also works with the prose aperture
--   - reading: "Let $V\Lambda V'$ denote the spectral decomposition of $M$" ($p\ge3$) → first column the eigenvector of the positive eigenvalue with positive first entry, other columns paired with $\widetilde W$ as in the published `IsConeUpdate`; reason: the page leaves the column order open; restricting the allowed outputs only strengthens an existence statement, and the counterexample never reaches $p\ge3$
--   - encoding: the first period with a nonzero effective difference is $t_0=1$ (p. 22) → the state stays empty and the policy plays $e_1$ until the first nonzero difference; reason: same runs when $t_0=1$, and defined otherwise
--   - encoding: the paper's periods $1,\dots,T$, $\Pi_\Delta$, $U^{-1}$, $\ln$ → Lean periods $0,\dots,T-1$, $B'B\delta$, $U^{\mathsf T}$, `Real.log`; reason: Lean conventions that change no instance ($B$ has orthonormal rows spanning $\Delta$, $U$ is orthonormal)
--   - encoding: "for any set $C_0$" with $c^\star\in C_0$ → $c^\star\in S^d$; reason: one admissible $C_0$ ($C_0=S^d$, closed) suffices to refute a bound claimed for every $C_0$, and the algorithm does not read $C_0$
--   - encoding: Algorithm 4 runs for $T$ periods → `IsProjConesRun` holds for all natural periods; reason: any finite run extends after $T$ using zero contexts and singleton action sets, so the same regret witness is available
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 26, Theorem 4; Algorithms 1, 3, 4 on pp. 19, 26, 28; proof App-15–App-22

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Supplement_Run
import Definitions.Def_CtxInvOpt_Greedy_Online

namespace CtxInvOpt.Offline.Supplement

theorem theorem4_projected_cones_regret_false :
    ∀ (d n : ℕ), 2 ≤ d → 1 ≤ n → ∀ (K : ℝ) (T0 : ℕ),
      ∃ T : ℕ, T0 ≤ T ∧ 0 < T ∧
        ∃ (cstar : EuclideanSpace ℝ (Fin d)) (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
          (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (S : ℕ → Option (PCFrame d)),
          cstar ∈ CtxInvOpt.Offline.unitSphere d ∧
          (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) ∧
          (∀ t, CtxInvOpt.Offline.IsContext (f t)) ∧
          IsProjConesRun ((d : ℝ) / T) ((d : ℝ) / T / (2 * d)) cstar X f xpi xstar S ∧
          K * (d : ℝ) ^ 4 * Real.log T < CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T := by sorry

end CtxInvOpt.Offline.Supplement
