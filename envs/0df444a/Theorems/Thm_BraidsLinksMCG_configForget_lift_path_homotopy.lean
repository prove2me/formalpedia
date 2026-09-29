-- Prove2me | Theorems.Thm_BraidsLinksMCG_configForget_lift_path_homotopy
-- name    : BraidsLinksMCG.configForget_lift_path_homotopy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T06:49:52.104958+00:00
-- url     : https://prove2.me/theorems/6b9deec6-e186-482f-8179-ea96953a651f
-- title:
--   Lift based path homotopies through the configuration-space projection
-- statement:
--   Let $p:F_{0,n+1}(\mathbb C)\to F_{0,n}(\mathbb C)$ forget the last point, with base configurations $(1,\ldots,n+1)$ and $(1,\ldots,n)$. Let $\gamma$ be a based loop upstairs, $\eta$ a based loop downstairs, and let $H$ be a homotopy relative to the endpoints from $p\circ\gamma$ to $\eta$. Then there exist a based loop $\delta$ upstairs and a homotopy $K$ relative to endpoints from $\gamma$ to $\delta$ such that
--   $$p(K(s,t))=H(s,t)\qquad(s,t\in[0,1]).$$
--   This is the relative homotopy lifting consequence of the Fadell--Neuwirth locally trivial bundle construction. The lift agrees with $\gamma$ at $s=0$ and with the fixed base point on both sides $t=0,1$. In particular, if $\eta$ is constant, the final loop $\delta$ lies in the fibre over the base configuration. The statement retains the entire lifted homotopy, rather than just its homotopy class. For $n=0$ the projection has one-point base and the assertion is immediate.
-- source:
--   Derived relative homotopy lifting consequence of the Fadell--Neuwirth bundle construction: Edward Fadell and Lee Neuwirth, Configuration Spaces, Math. Scand. 10 (1962), Theorem 1 and local product construction, pp. 111–112, https://doi.org/10.7146/math.scand.a-10517; applied to forgetting the last coordinate as in Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4. This relative lifting formulation is a corollary, not a verbatim statement of Theorem 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem configForget_lift_path_homotopy (n : ℕ)
    (γ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)))
    (η : Path (baseOrdered n) (baseOrdered n))
    (H : ((γ.map (configForget n).continuous).cast
      (configForget_base n).symm (configForget_base n).symm).Homotopy η) :
    ∃ δ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)),
      ∃ K : γ.Homotopy δ,
        ∀ s t, configForget n (K (s, t)) = H (s, t) := by sorry

end BraidsLinksMCG
