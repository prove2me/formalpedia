-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_5_1
-- name    : ActorCritic.Finite.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:40.259425+00:00
-- url     : https://prove2.me/theorems/1fb8b4e1-53dc-4ef8-9aac-056c998890d8
-- title:
--   Lemma 5.1 — T_θ and the regenerative Q_θ are well defined and bounded uniformly in θ
-- statement:
--   Let $(\mathbb X,\mathbb U,p,c)$ be a finite cost MDP and $\mu_\theta$ a family of RSPs satisfying Assumption 2.1 with data $N$, $x^*$, $\epsilon_0$. Let $\tau=\min\{k>0\mid X_k=x^*\}$ be the first return time to $x^*$ of the chain under the fixed RSP $\theta$, and
--   $$
--   T_\theta(x,u)=\mathbf E_{\theta,x}[\tau\mid U_0=u],\qquad Q_\theta(x,u)=\mathbf E_{\theta,x}\Big[\sum_{k=0}^{\tau-1}\big(c(X_k,U_k)-\bar\alpha(\theta)\big)\,\Big|\,U_0=u\Big].
--   $$
--   Then for every $\theta$ and $(x,u)$ the series $\sum_k(\tilde P_\theta^k\underline1)(x,u)$ and $\sum_k(\tilde P_\theta^k(c-\bar\alpha(\theta)\underline1))(x,u)$ that represent $T_\theta(x,u)$ and $Q_\theta(x,u)$ converge, and there is a constant $B$ with
--   $$
--   |T_\theta(x,u)|\le B,\qquad |Q_\theta(x,u)|\le B\qquad\text{for all }\theta,x,u.
--   $$
--
--   In the paper's language, both families belong to the class $\mathcal D$; this is what makes the TD(1) steady-state quantities $\bar Z(\theta)$ and $\bar h_1(\theta)$ bounded in $\theta$.
--
--   **Formalization Note** For finite $\mathbb X$, $\mathbb U$, membership in $\mathcal D$ amounts to boundedness uniform in $\theta$. $\tilde P_\theta$ is the taboo matrix $\tilde P_\theta((x,u),(y,\bar u))=p(y\mid x,u)\mu_\theta(\bar u\mid y)1\{y\ne x^*\}$, for which $\mathbf P_{\theta,x}(\tau>k\mid U_0=u)=(\tilde P_\theta^k\underline1)(x,u)$. Assumption 4.9 of §5.1 enters this lemma in the paper only through $\mathbb X_0=\{x^*\}$, automatic in the finite case, and is not assumed.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1157, Lemma 5.1 (definitions of τ, T_θ, Q_θ, p. 1157)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

namespace ActorCritic.Finite

/-- **Lemma 5.1** (Konda–Tsitsiklis 2003, p. 1157), finite case: the families `T_θ` and `Q_θ`
(regenerative, `τ` = first return to `x*`) belong to `𝒟`, which for finite `X`, `U` means
they are well defined and bounded uniformly in `θ`. Under Assumption 2.1 (with data `N`, `x*`,
`ε₀`): for every `θ` and `(x, u)` the series `∑_k (P̃_θ^k 1)(x, u)` and
`∑_k (P̃_θ^k (c − ᾱ(θ) 1))(x, u)` defining `T_θ(x, u)` and `Q_θ(x, u)` converge, and there is
`B` with `|T_θ(x, u)| ≤ B` and `|Q_θ(x, u)| ≤ B` for all `θ, x, u`. -/
theorem lemma_5_1
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    {n : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀) :
    (∀ (θ : EuclideanSpace ℝ (Fin n)) (w : X × U),
      Summable (fun k : ℕ => (tabooMatrix M π xstar θ ^ k).mulVec (fun _ => 1) w) ∧
      Summable (fun k : ℕ =>
        (tabooMatrix M π xstar θ ^ k).mulVec (fun w' => M.c w'.1 w'.2 - avgCost M π θ) w)) ∧
    ∃ B : ℝ, ∀ (θ : EuclideanSpace ℝ (Fin n)) (w : X × U),
      |returnTime M π xstar θ w| ≤ B ∧ |Qreg M π xstar θ w| ≤ B := by sorry

end ActorCritic.Finite
