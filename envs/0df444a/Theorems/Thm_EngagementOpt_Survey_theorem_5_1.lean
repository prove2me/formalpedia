-- Prove2me | Theorems.Thm_EngagementOpt_Survey_theorem_5_1
-- name    : EngagementOpt.Survey.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:56.417585+00:00
-- url     : https://prove2.me/theorems/6374d318-92bc-4bc0-8f84-598c25b3c1e9
-- title:
--   Theorem 5.1: monotonicity of $\mathbb E[S\mid T=t]$ in the session length
-- statement:
--   A user's session has two phases. System 2 enjoys $T_q\sim\mathrm{Geom}(1-q)$ items, after which system 1 keeps the user on for $T_p\sim\mathrm{Geom}(1-p)$ further steps (counting the first), with $T_q,T_p$ independent on $\{1,2,\dots\}$; the session length is $T=T_q+T_p-1$. Each enjoyed item has mean value $\bar v$ and each step costs the outside option $W$, so that (8)–(9)
--
--   $$
--   f(t):=\mathbb E[S\mid T=t]=\bar v\,\mathbb E[T_q\mid T=t]-Wt,\qquad t\in\{1,2,\dots\}.
--   $$
--
--   Assume $0<p<1$, $0<q<1$, $\bar v\ge0$ and $W>0$. "Increasing" means $f(t)<f(t+1)$ and "decreasing" means $f(t+1)<f(t)$. Then:
--
--   1. **$q=p$.** $f(t)<f(t+1)$ for all $t\ge1$ if and only if $\bar v>2W$.
--   2. **$q>p$.**
--      (a) If $\bar v>2W$, then $f(t)<f(t+1)$ for all $t\ge1$.
--      (b) If $\bar v>W$, there is $t^*$ such that $f(t)<f(t+1)$ for all $t>t^*$.
--   3. **$q<p$.**
--      (a) If $\bar v<2W$, then $f(t+1)<f(t)$ for all $t\ge1$.
--      (b) There is $t^*$ such that $f(t+1)<f(t)$ for all $t>t^*$.
--
--   A platform that observes post-session survey utility and session lengths can therefore read off whether its content has longer span than moreishness ($q>p$) or the reverse.
--
--   **Formalization Note** The hypotheses $0<p<1$, $0<q<1$ are the paper's standing assumptions (§2.1: "for some $q>0$", "probability $p>0$"; the parameter space has $p,q<1$). The parameter space on p. 15 has $\bar v\in\mathbb R_+$; $W>0$ is implicit (§2.1 normalizes $W=1$). The hypothesis $\bar v>W$ in 2(b) is not printed in the theorem but is used in its proof on p. 22 ("since $\bar v>W$ by assumption"); without it 2(b) is false, since the per-step growth of $\bar v\,\mathbb E[T_q\mid T=t]$ stays below $\bar v$. Session lengths are natural numbers $t\ge1$, the support of $T$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 19, Theorem 5.1 (hypothesis v̄ > W in 2(b) from the proof, p. 22)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_condUtility

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 19, Theorem 5.1. Let `f(t) = E[S | T = t]` (`condUtility`) for session
lengths `t ≥ 1`, with `0 < p < 1`, `0 < q < 1`, `v̄ ≥ 0` and `W > 0`.
1. If `q = p`, then `f` is (strictly) increasing on `t ≥ 1` iff `v̄ > 2W`.
2. If `q > p`: (a) if `v̄ > 2W`, `f` is increasing for all `t ≥ 1`;
   (b) if `v̄ > W` (the hypothesis used in the proof, p. 22), `f` is increasing for `t > t*`.
3. If `q < p`: (a) if `v̄ < 2W`, `f` is decreasing for all `t ≥ 1`;
   (b) `f` is decreasing for `t > t*`. -/
theorem theorem_5_1 (p q v W : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hv : 0 ≤ v) (hW : 0 < W) :
    (q = p →
      ((∀ t : ℕ, 1 ≤ t → condUtility v W p q t < condUtility v W p q (t + 1)) ↔ 2 * W < v)) ∧
    (p < q → 2 * W < v →
      ∀ t : ℕ, 1 ≤ t → condUtility v W p q t < condUtility v W p q (t + 1)) ∧
    (p < q → W < v →
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ < t → condUtility v W p q t < condUtility v W p q (t + 1)) ∧
    (q < p → v < 2 * W →
      ∀ t : ℕ, 1 ≤ t → condUtility v W p q (t + 1) < condUtility v W p q t) ∧
    (q < p →
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ < t → condUtility v W p q (t + 1) < condUtility v W p q t) := by sorry

end EngagementOpt.Survey
