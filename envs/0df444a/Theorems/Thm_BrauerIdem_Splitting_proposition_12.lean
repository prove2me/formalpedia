-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_proposition_12
-- name    : BrauerIdem.Splitting.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:10.591312+00:00
-- url     : https://prove2.me/theorems/04cfa69f-fff3-4dc0-9992-d28bd0aaf1b9
-- title:
--   Proposition 12, p. 8 — ūA_t = A_t, and ūA = δ^r A_t with A ≠ A_t forces r < 0
-- statement:
--   Let $\ell<n$ with $n-\ell$ even, and let $u=u_1u_3\cdots u_{n-\ell-1}$ be the Brauer diagram with northern and southern arcs $\{2j+1,2j+2\}$ for $j=0,1,\dots,\tfrac12(n-\ell-2)$ and vertical lines $\{i,i'\}$ for $i>n-\ell$. Put $\bar u=\delta^{-(n-\ell)/2}u$. Let $A_{\mathfrak t}$ be a Brauer diagram that has a northern arc between nodes $2j+1$ and $2j+2$ for every $j=0,\dots,\tfrac12(n-\ell-2)$. For a diagram $A$, the product is $\bar uA=\delta^{r}\pi(u\circ A)$ with
--
--   $$
--   r=v(u,A)-\tfrac12(n-\ell),
--   $$
--
--   where $v(u,A)$ is the number of closed loops formed. Then:
--
--   1. $\bar uA_{\mathfrak t}=A_{\mathfrak t}$, that is, $\pi(u\circ A_{\mathfrak t})=A_{\mathfrak t}$ and $v(u,A_{\mathfrak t})=\tfrac12(n-\ell)$;
--   2. (Proposition 12) if $A\neq A_{\mathfrak t}$ and $\bar uA=\delta^rA_{\mathfrak t}$ for some $r\in\mathbb Z$, then $r<0$.
--
--   Together these make the coefficient of $A_{\mathfrak t}$ in $\bar uX$ have leading term $c_{\mathfrak t}$, which is what makes the linear system (6) nonsingular.
--
--   **Formalization Note** Lean nodes are 0-based, so the paper's arc $\{2j+1,2j+2\}$ is $\{2j,2j+1\}$. The statement is phrased with the unnormalised $u$: $\bar uA=\delta^rA_{\mathfrak t}$ holds exactly when $\pi(u\circ A)=A_{\mathfrak t}$ and $r=v(u,A)-\tfrac12(n-\ell)$, so $r<0$ becomes $v(u,A)<\tfrac12(n-\ell)$. The diagrams $A$, $A_{\mathfrak t}$ are unnormalised, as on the page. The evenness of $n-\ell$ is added, because the product $u_1u_3\cdots u_{n-\ell-1}$ presupposes it.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 8, §3, sentence before Proposition 12 and Proposition 12

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, §3, p. 8 (`ūA_t = A_t`) and Proposition 12. `B` plays `A_t`: it has
northern arcs between the paper's nodes `2j+1, 2j+2` (0-based `2j, 2j+1`) for
`j = 0, …, (n-l-2)/2`. With `ū = δ^{-(n-l)/2} u`, `ūA = δ^r π(u∘A)` where
`r = loops u A - (n-l)/2`. -/
theorem proposition_12 (n l : ℕ) (hl : l < n) (hpar : Even (n - l)) (B : Diagram n)
    (hB : ∀ i j : Fin n, i.val % 2 = 0 → j.val = i.val + 1 → j.val < n - l →
      B.1 (.inl i) = .inl j) :
    (IsComposite (uDiag n l) B B ∧ loops (uDiag n l) B = (n - l) / 2) ∧
    ∀ A : Diagram n, A ≠ B → IsComposite (uDiag n l) A B →
      loops (uDiag n l) A < (n - l) / 2 := by sorry

end BrauerIdem.Splitting
