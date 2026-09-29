-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_trajControllable_iff_irreducible
-- name    : DelayedBCN.Controllability.trajControllable_iff_irreducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:06:55.397762+00:00
-- url     : https://prove2.me/theorems/4007406d-effd-44e8-b49c-c931788bcc08
-- title:
--   Theorem 3.10 — a delayed BCN is trajectory controllable iff Q is irreducible
-- statement:
--   Consider a delayed Boolean control network (2.2) with $n$ state nodes, $m$ inputs, delay length $\mu\ge1$ and arbitrary update functions, and let $Q$ be its transition-count matrix ($Q_{b,a}$ = number of input values taking trajectory $a$ to trajectory $b$ in one step). Then
--
--   $$
--   \text{the network is trajectory controllable}\iff Q \text{ is irreducible}.
--   $$
--
--   Trajectory controllability is Definition 3.1: for every initial trajectory $X(0)$ and every trajectory $X_d$ there are $k\ge1$ and a control sequence of length $k$ with $X(k)=X_d$. Irreducibility is Definition 3.7, applied to $Q$ with its entries viewed as real numbers.
--
--   The theorem replaces a search over control sequences of unbounded length by a finite matrix test.
--
--   **Formalization Note** Controllability is defined through the dynamics and control sequences, not through powers of $Q$. The step count in Definition 3.1 is $k\ge1$ (see the model file). No assumption on $n$, $m$ or the update functions is made.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 486, Theorem 3.10

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Theorem 3.10 (Lu et al. 2016, p. 486): the delayed BCN is trajectory controllable
(Definition 3.1) if and only if `Q` is irreducible (Definition 3.7). -/
theorem trajControllable_iff_irreducible {μ n m : ℕ} [NeZero μ] (F : Network μ n m) :
    TrajControllable F ↔ IsIrreducibleMat ((Q F).map (fun x : ℕ => (x : ℝ))) := by sorry

end DelayedBCN.Controllability
