-- Prove2me | Theorems.Thm_DenardoDP_NStage_sup_modulus_le
-- name    : DenardoDP.NStage.sup_modulus_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:59:44.085896+00:00
-- url     : https://prove2.me/theorems/0bc1cb25-0ec4-4a19-8d70-aefcd2d6c88b
-- title:
--   §3 observation — a pointwise supremum of operators of modulus ≤ c has modulus ≤ c
-- statement:
--   Let $V$ be the space of bounded real functions on a set $\Omega$ with the sup metric $\rho$. Let $I$ be a nonempty index set and let $\{B_\alpha:\alpha\in I\}$ be operators on $V$, each of modulus $c$ or less, i.e. $\rho(B_\alpha u,B_\alpha v)\le c\,\rho(u,v)$ for all $u,v\in V$. Suppose the operator $E$ defined by
--   $$(Ev)(x)=\sup_{\alpha\in I}(B_\alpha v)(x)$$
--   maps $V$ into $V$. Then $E$ has modulus $c$ or less:
--   $$\rho(Eu,Ev)\le c\,\rho(u,v)\qquad\text{for all }u,v\in V.$$
--
--   In §5 of the paper this observation, applied to the operators $B_\delta=H_\delta^N$, shows that $E$ is a contraction mapping; it is part (c) of Theorem 4.
--
--   **Formalization Note** The hypothesis "$E$ has range contained in $V$" is encoded by taking $E$ as a function $V\to V$ whose value at each point is the least upper bound (`IsLUB`) of $\{(B_\alpha v)(x):\alpha\in I\}$.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 168, §3, observation following Corollary 2

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

namespace DenardoDP.NStage

theorem sup_modulus_le {Ω : Type*} {I : Type*} [Nonempty I] (B : I → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (c : ℝ) (hB : ∀ α, DenardoDP.Contraction.ModulusLE (B α) c)
    (hE : ∀ w x, IsLUB (Set.range fun α => B α w x) (E w x)) :
    DenardoDP.Contraction.ModulusLE E c := by sorry

end DenardoDP.NStage
