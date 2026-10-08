-- Prove2me | Theorems.Thm_AlgebraicPCSP_Colouring_theorem_6_2
-- name    : AlgebraicPCSP.Colouring.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:19.325538+00:00
-- url     : https://prove2.me/theorems/85e1f82f-bf21-4f6a-9d1b-83128e2dc6d8
-- title:
--   Theorem 6.2 — M maps to Pol(H₂, H_K) for some K ≥ 2 iff M contains no Olšák function
-- statement:
--   Let $\mathscr M$ be a minion on a pair of finite sets $(A, B)$, and for $K \ge 2$ let $\mathscr H_K = \mathrm{Pol}(\mathbf H_2, \mathbf H_K)$, where $\mathbf H_K = (E_K; \mathrm{NAE}_K)$. The following are equivalent:
--
--   1. there exist $K \ge 2$ and a minion homomorphism $\xi : \mathscr M \to \mathscr H_K$;
--   2. $\mathscr M$ does not contain an Olšák function, i.e. no 6-ary $o \in \mathscr M$ satisfies
--   $$
--   o(x, x, y, y, y, x) = o(x, y, x, y, x, y) = o(y, x, x, x, y, y) \quad \text{for all } x, y \in A .
--   $$
--
--   Combined with the hardness of approximate hypergraph colouring, this gives a purely algebraic sufficient condition for NP-hardness of a PCSP (Corollary 6.3): it suffices that the template has no Olšák polymorphism.
--
--   **Formalization Note** The minion's sets are finite (`Fintype A`, `Fintype B`), the paper's standing assumption on minions (Definition 2.20); it makes the set $\mathscr M^{(2)}$ of binary members finite. The target minion is exactly $\mathrm{Pol}(\mathbf H_2, \mathbf H_K)$ with $K \ge 2$ quantified existentially.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 38, Theorem 6.2

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- Theorem 6.2 (arXiv:1811.00970v3, p. 38): for a minion `M` on finite sets `(A, B)`, the
following are equivalent:
(1) there exist `K ≥ 2` and a minion homomorphism `M → 𝓗_K = Pol(H₂, H_K)`;
(2) `M` does not contain an Olšák function. -/
theorem theorem_6_2 {A B : Type} [Fintype A] [Fintype B] (M : Minion A B) :
    (∃ (K : ℕ) (hK : 2 ≤ K)
        (ξ : (n : ℕ) → ((Fin n → A) → B) → ((Fin n → Fin 2) → Fin K)),
        IsMinionHom M (HMinion K hK) ξ) ↔
      ¬ ContainsOlsak M := by sorry

end AlgebraicPCSP.Colouring
