-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_step_d_kl_bound
-- name    : FirstPriceLearning.ContextLowerBound.step_d_kl_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T06:44:04.004404+00:00
-- url     : https://prove2.me/theorems/01da93c0-4830-463e-8590-783593ce2bf0
-- title:
--   Step (d), p. 23: chain rule of KL + property 5 give $D_{\mathrm{KL}}((P^{u^c})^{\otimes t}\|(P^u)^{\otimes t})\le\frac{64}{3}\Delta^2\sum_{s<t}\mathbb P_{u^c}(i_s<c \text{ or } a_s=(c,u_c))$
-- statement:
--   Fix integers $\alpha, M\ge 0$ and a horizon $T\ge (\alpha+1)M$, and let $\Delta=\sqrt{K/(16T)}$ with $K=(\alpha+1)M$. Let $\pi$ be any randomized non-anticipating policy (internal randomness $\omega_U\sim\mu_U$) on the action set $\mathcal A=[M]\times\{0,1,\dots,\alpha\}$ of the hard instances of Theorem 6, run against an arbitrary oblivious context sequence $(c_s)_{s\le T}$ with the feedback graph $G$ (cross learning: when $a$ is played, the rewards of all $b$ with $b=a$ or $(a,b)\in G$ are revealed under every context).
--
--   Let $u\in\{0,\dots,\alpha\}^M$ and a context $c$ with $u_c\neq 0$, and let $u^c$ be $u$ with its $c$-th coordinate set to $0$. For $t\le T$, write $(P^{u})^{\otimes t}$ for the joint law of the internal randomness and of all observations of the first $t$ rounds when the rewards are i.i.d. $\sim P^u$. Then (chain rule of KL divergence combined with property 5)
--   $$D_{\mathrm{KL}}\big((P^{u^c})^{\otimes t}\,\big\|\,(P^{u})^{\otimes t}\big)\ \le\ \frac{64}{3}\Delta^2\sum_{s<t}\mathbb P_{u^c}\big(i_s<c\ \text{ or }\ (i_s,j_s)=(c,u_c)\big),$$
--   where $a_s=(i_s,j_s)$ is the action of round $s$ (rounds indexed from $0$ in Lean) and the probability is under $P^{u^c}$.
--
--   This is the bound used in step (d) of the proof of Theorem 6: by the chain rule, the divergence is the sum over rounds $s<t$ of the expected KL divergence between the observed reward laws $P^{u^c}(a_s)$ and $P^{u}(a_s)$, and by property 5 each term is at most $\frac{64}{3}\Delta^2\,\mathbb 1(i_s<c \text{ or } a_s=(c,u_c))$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 23, proof of Theorem 6, step (d) ("follows from the chain rule of KL divergence and the fifth property of mean rewards")

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory InformationTheory

namespace FirstPriceLearning.ContextLowerBound

theorem step_d_kl_bound (M α T : ℕ) (hT : (α + 1) * M ≤ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) (ctx : Fin T → Fin M) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (hu : u c ≠ 0) (t : ℕ) (ht : t ≤ T) :
    klDiv ((interactionLaw μU (hardLaw M α T (Function.update u c 0)) T).map
          (fun ω => (ω.1, observations (feedbackGraph M α) π ctx ω.1 ω.2 t ht)))
        ((interactionLaw μU (hardLaw M α T u) T).map
          (fun ω => (ω.1, observations (feedbackGraph M α) π ctx ω.1 ω.2 t ht))) ≤
      ENNReal.ofReal (64 / 3 * gap M α T ^ 2 *
        ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
          (interactionLaw μU (hardLaw M α T (Function.update u c 0)) T
            {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 s).1 < c ∨
              action (feedbackGraph M α) π ctx ω.1 ω.2 s = (c, u c)}).toReal) := by sorry

end FirstPriceLearning.ContextLowerBound
