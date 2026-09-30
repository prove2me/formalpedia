-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_claim_4_11
-- name    : AlgMechDesign.Additive.claim_4_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:22:45.062533+00:00
-- url     : https://prove2.me/theorems/eb7f735b-79e9-4781-9da2-06ef0afa0b3c
-- title:
--   Claim 4.11 — lowering agent $i$'s times keeps every task of $x^i(t)$ with agent $i$
-- statement:
--   Let $m=(x,p)$ be a truthful additive mechanism for task scheduling, and let $t$ be the type vector with $t^{i'}_j = 1$ for every agent $i'$ and task $j$. Fix an agent $i$, let $x = x^i(t)$ and let $\bar x$ be its complement. For $0<\epsilon<1$ let
--
--   $$\hat t = t\bigl(x \xrightarrow{i} 1-\epsilon,\ \bar x \xrightarrow{i} \epsilon\bigr),$$
--
--   the type vector obtained from $t$ by setting $\hat t^i_j = 1-\epsilon$ for $j\in x$ and $\hat t^i_j = \epsilon$ for $j\notin x$, all other agents unchanged. Assume that the empty set is attainable for agent $i$ against $t^{-i}$ (some positive declaration of agent $i$ makes the mechanism give it no task). Then
--
--   $$x^i(\hat t) \supseteq x^i(t).$$
--
--   In the proof of Theorem 4.10 this is applied to an agent holding at least $n$ tasks at $t$, and it forces that agent to keep them after its times drop.
--
--   **Formalization Note** The paper states the claim for agent $1$ after a relabelling; here it is stated for an arbitrary agent $i$. The hypothesis that $\emptyset$ is attainable is added: without it the claim as printed is false (a mechanism that always gives agent $i$ exactly its $|x|$ cheapest tasks and pays nothing is truthful and additive, and at $\hat t$ with $\epsilon<1/2$ and $k>|x|$ it trades a task of $x$ for a cheaper task of $\bar x$). The paper's proof uses it implicitly through "the price offered to agent 1 for $x$ is strictly greater than $\hat t^1(x)$". Under the hypothesis of Theorem 4.10 that the mechanism is a $c$-approximation, $\emptyset$ is attainable for every agent when $n\ge 2$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, Claim 4.11 (with the notation t(X →^i α) of p. 179)

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model
import Definitions.Def_AlgMechDesign_Additive_Price

namespace AlgMechDesign.Additive

/-- Claim 4.11, p. 180, for an arbitrary agent `i`: let `t` be the all-ones type vector,
`x = xⁱ(t)`, `0 < ε < 1` and `t̂ = t(x →ⁱ 1 - ε, x̄ →ⁱ ε)`. For a truthful additive mechanism
under which the empty set is attainable for agent `i` against `t⁻ⁱ`, `xⁱ(t̂) ⊇ xⁱ(t)`. -/
theorem claim_4_11 {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hadd : IsAdditive alloc pay) (i : Fin n)
    (hempty : IsAttainable alloc i (fun _ _ => (1 : ℝ)) ∅)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    taskSet (alloc (fun _ _ => (1 : ℝ))) i ⊆
      taskSet (alloc (Function.update (fun _ _ => (1 : ℝ)) i
        (fun j => if j ∈ taskSet (alloc (fun _ _ => (1 : ℝ))) i then 1 - ε else ε))) i := by sorry

end AlgMechDesign.Additive
