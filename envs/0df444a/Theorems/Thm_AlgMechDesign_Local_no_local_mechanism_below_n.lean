-- Prove2me | Theorems.Thm_AlgMechDesign_Local_no_local_mechanism_below_n
-- name    : AlgMechDesign.Local.no_local_mechanism_below_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T20:05:12.477798+00:00
-- url     : https://prove2.me/theorems/fbdc7eb5-1ad2-4877-9012-6147103ff855
-- title:
--   Theorem 4.12 — no local truthful mechanism is a c-approximation for task scheduling for any c < n
-- statement:
--   Consider task scheduling on $n \ge 1$ unrelated agents with $k \ge n^2$ tasks. Let $(x, p)$ be a truthful direct mechanism which is local: the price $p^i(X, t^{-i})$ offered to each agent $i$ for each set $X$ of tasks depends only on the other agents' times on the tasks of $X$. Then for every real $c < n$ the allocation rule $x$ is not a $c$-approximation of the make-span: there are a positive type vector $t$ and an allocation $y$ with
--   $$
--   g(x(t), t) > c \cdot g(y, t).
--   $$
--
--   Together with the mechanism MinWork, which is local, truthful and an $n$-approximation, this shows that $n$ is the best ratio a local truthful mechanism can achieve, confirming Conjecture 4.9 for this class of mechanisms.
--
--   **Formalization Note** The paper states the theorem without a bound on the number of tasks; its proof takes $k \ge n^2$, which is the hypothesis here. Following §4.3 ("m = (x, p) is always assumed to be a truthful mechanism"), the mechanism is assumed truthful; by the revelation principle this covers every implementation. Types and declarations are positive. Locality is Definition 14 applied to the price function of Definition 12, including its value $0$ for sets the agent cannot obtain.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, Theorem 4.12 (proof p. 181)

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Theorem 4.12, p. 180: there does not exist a local truthful mechanism for task scheduling
that is a `c`-approximation for any `c < n` (with `k ≥ n²` tasks, as in the proof). -/
theorem no_local_mechanism_below_n (n k : ℕ) [NeZero n] (hk : n ^ 2 ≤ k) (c : ℝ)
    (hc : c < n) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hloc : IsLocal alloc pay) : ¬ IsApprox c alloc := by sorry

end AlgMechDesign.Local
