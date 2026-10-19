-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_proposition_2
-- name    : DERAggregation.Unregulated.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:06.119991+00:00
-- url     : https://prove2.me/theorems/dfe6598f-55ba-442f-98e0-fa7cf100a856
-- title:
--   Proposition 2, p. 12 — the offers (17a)–(17b) with responses (17c) form a Stackelberg equilibrium of G(λ)
-- statement:
--   Consider the networked market under Assumption 1, and a vector $\lambda$ of wholesale prices that is positive at every node hosting a prosumer. Then for each prosumer $i$ there is $z_i\in(0,Z)$ with $u_i'(z_i)=\lambda^{k(i)}$, and for every such choice the offers and responses
--   $$P_i^*=\big[\lambda^{k(i)}(C_i-z_i)+u_i(z_i)-u_i(C_i)\big]^+,\qquad p_i^*=\lambda^{k(i)},\tag{17a–b}$$
--   $$x_i^*=[C_i-z_i]^+,\qquad d_i^*=[z_i-C_i]^+ \tag{17c}$$
--   constitute a Stackelberg equilibrium of the game $\mathcal G(\lambda)$ (Definition 1): each $(x_i^*,d_i^*)$ is an optimal response to $(P_i^*,p_i^*)$, and no nonnegative offer vector earns the aggregator more total profit against any optimal responses.
--
--   This is the economically efficient equilibrium of the aggregator–prosumer game: the aggregator makes no margin on energy and earns its profit only through the participation fees.
--
--   **Formalization Note** The paper states the proposition for any $\lambda$; the roots $z_i$ exist only for positive prices (Assumption 1 gives $u_i'>0$), so positivity is assumed.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 12, Definition 1, Proposition 2, (17a)–(17c)

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Proposition 2 (p. 12). Under Assumption 1 and positive wholesale prices, roots `z_i` of
`u_i'(z_i) = λ^{loc i}` exist, and for every such choice the offers (17a)–(17b) with the responses
(17c) and `d*_i = [z_i − C_i]⁺` form a Stackelberg equilibrium of `G(λ)`. -/
theorem proposition_2 {K I J L : Type} [Fintype I] (M : Market K I J L) (h1 : Assumption1 M)
    (lam : K → ℝ) (hlam : ∀ i, 0 < lam (M.loc i)) :
    (∃ zz : I → ℝ, ∀ i, zz i ∈ Ioo 0 M.Z ∧ deriv (M.u i) (zz i) = lam (M.loc i)) ∧
    ∀ zz : I → ℝ, (∀ i, zz i ∈ Ioo 0 M.Z ∧ deriv (M.u i) (zz i) = lam (M.loc i)) →
      IsStackelberg M lam
        (fun i => max (lam (M.loc i) * (M.C i - zz i) + M.u i (zz i) - M.u i (M.C i)) 0)
        (fun i => lam (M.loc i))
        (fun i => max (M.C i - zz i) 0)
        (fun i => max (zz i - M.C i) 0) := by sorry

end DERAggregation.Unregulated
