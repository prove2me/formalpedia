-- Prove2me | Theorems.Thm_AssortOpt_HMF_opt_policy_assortment
-- name    : AssortOpt.HMF.opt_policy_assortment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:22.151995+00:00
-- url     : https://prove2.me/theorems/6650e13f-2043-4866-a19e-9417886af129
-- title:
--   Proof of Theorem 2, §E.2, p. 43 — under history-monotone futures some optimal monotone stopping policy is an assortment (OPT^φ = OPT^S)
-- statement:
--   Suppose the list distribution $\mathcal L, p$ has history-monotone futures, and let $r_j \ge 0$ be any prices. Then there is an assortment $S$ whose stopping policy ($\phi_j \equiv 1$ for $j \in S$, $\phi_j \equiv 0$ otherwise) is optimal among all monotone stopping policies:
--   $$\mathsf{REV}[\phi^S] = \max_{\phi \text{ monotone}} \mathsf{REV}[\phi] = \mathsf{OPT}^\phi, \qquad \mathsf{REV}[\phi^S] = \mathsf{REV}[S].$$
--
--   Together with $\mathsf{OPT}^x \le \mathsf{OPT}^f \le \mathsf{OPT}^\phi$ (Propositions 2 and 3), this is the core of the proof of the paper's main result: the relaxation chain collapses, $\mathsf{OPT}^S = \mathsf{OPT}^\phi$.
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - reading: "at least one of these optimal policies $\phi$ corresponds to offering an assortment" → for some $S$, the policy of $S$ attains the maximum of $\mathsf{REV}[\phi]$ over monotone policies, and its revenue is $\mathsf{REV}[S]$; reason: the page's correspondence (p. 13) of assortments with constant policies, with the revenue identity it asserts.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 43, proof of Theorem 2 (§E.2), first paragraph; p. 13 (assortments as constant policies)

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem opt_policy_assortment {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n),
      IsGreatest (revPolicy D r '' {φ | IsMonotonePolicy φ}) (revPolicy D r (assortPolicy S)) ∧
      revPolicy D r (assortPolicy S) = revAssort D r S := by sorry

end AssortOpt.HMF
