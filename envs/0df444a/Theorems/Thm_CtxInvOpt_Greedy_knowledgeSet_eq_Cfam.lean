-- Prove2me | Theorems.Thm_CtxInvOpt_Greedy_knowledgeSet_eq_Cfam
-- name    : CtxInvOpt.Greedy.knowledgeSet_eq_Cfam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:08.391605+00:00
-- url     : https://prove2.me/theorems/93485e37-d1d0-4561-8cfc-ad53a6462a97
-- title:
--   App-9–App-10, proof of Theorem 2, Step 2 — under π_greedy the knowledge sets are C(𝓘_t) = C_{ε_{t−1},ᾱ}
-- statement:
--   Fix $0<\bar\alpha<\pi/2$ and a horizon $T\ge1$. Take $d=n=3$, initial knowledge set $C_0=C_{0,\bar\alpha}$, true cost $c^\star=(\cos\bar\alpha,\sin\bar\alpha,0)$, identity contexts $f_t=\mathrm{id}$, and feasible sets $\mathcal X_t=\{\bar x_t,0\}$ with $\bar x_t=(e_2-\varepsilon_te_1)/\|e_2-\varepsilon_te_1\|$, $\varepsilon_t=t\varepsilon_1$, $\varepsilon_1=\tan\bar\alpha/(2T)$.
--
--   Then for every run of the greedy circumcenter policy (any circumcenter choice, any tie-break) the knowledge sets stay in the family:
--
--   $$C(\mathcal I_t)=C_{\varepsilon_{t-1},\bar\alpha}\qquad\text{for } t=1,\dots,T+1,$$
--
--   with $\varepsilon_0=0$. In particular the policy never learns enough to move its proxy cost close to $c^\star$.
--
--   **Formalization Note** Periods are $0$-based: Lean's knowledge set at period $t$ is the paper's $C(\mathcal I_{t+1})$, and the claim reads `knowledgeSet … t = Cfam (t * ε₁) a` for $0\le t\le T$. The run predicate quantifies over every circumcenter and every minimizer; no value of the circumcenter is hard-coded.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, App-9–App-10, proof of Theorem 2, Step 2

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Greedy_Policy
import Definitions.Def_CtxInvOpt_Greedy_Family

open Real

namespace CtxInvOpt.Greedy

/-- **arXiv:2106.14015v3, App-9–App-10, proof of Theorem 2, Step 2.** Fix `0 < ᾱ < π/2` and a
horizon `T ≥ 1`. Let `C₀ = C_{0,ᾱ}`, `c⋆ = (cos ᾱ, sin ᾱ, 0)`, `f_t = id` and
`X_t = {x̄_t, 0}` with `ε_t = t · tan ᾱ/(2T)`. Under every run of the greedy circumcenter policy the
knowledge set stays in the family: in Lean's 0-based period `t ≤ T` it is `C_{t ε₁, ᾱ}`
(the paper's `C(I_{t+1}) = C_{ε_t,ᾱ}`). -/
theorem knowledgeSet_eq_Cfam {a : ℝ} (ha0 : 0 < a) (ha1 : a < π / 2) {T : ℕ} (hT : 1 ≤ T)
    {xpi xstar chat : ℕ → EuclideanSpace ℝ (Fin 3)}
    (hrun : IsGreedyRun (Cfam 0 a) (cstarFam a) (instX a T) (fun _ => id) xpi xstar chat) :
    ∀ t ≤ T, knowledgeSet (Cfam 0 a) (instX a T) (fun _ => id) xstar t =
      Cfam ((t : ℝ) * eps1 a T) a := by sorry

end CtxInvOpt.Greedy
