-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_existence
-- name    : BrauerIdem.Splitting.existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:06.031375+00:00
-- url     : https://prove2.me/theorems/1754f53c-87c7-43b4-9455-6de085f0c129
-- title:
--   §3, p. 8 — for ℓ < n the splitting idempotent φ_n(ℓ) of J̄_n(ℓ) exists over K
-- statement:
--   Let $B_n=B_n(\delta)$ be the Brauer algebra on $n$ strands over $F=\mathbb Q(\delta)$, with basis the Brauer diagrams and product $AB=\delta^{v(A,B)}\pi(A\circ B)$. Let $J_n(\ell)$ be the two-sided ideal spanned by the diagrams with at most $\ell$ propagating lines, and let
--
--   $$
--   K=\{f/g : f,g\in\mathbb Z[\delta],\ g\text{ monic},\ \deg f\le\deg g\}\subseteq F .
--   $$
--
--   For every $\ell<n$ there is an element $\varphi_n(\ell)\in B_n$, all of whose diagram coefficients lie in $K$, such that
--
--   $$
--   \varphi_n(\ell)-1\in J_n(\ell),\qquad \varphi_n(\ell)\,d=d\,\varphi_n(\ell)=0\quad\text{for all } d\in J_n(\ell).
--   $$
--
--   By Lemma 10 this is the splitting idempotent of the sequence $0\to J_n(\ell)\to B_n\to B_n/J_n(\ell)\to0$. The paper asserts this on p. 8 ("We will see below that this idempotent exists for our chosen ring $K$"); it gives no separate proof, the existence over $F$ resting on the generic semisimplicity of $B_n(\delta)$ cited in its introduction.
--
--   This existence statement is what allows the paper to write $\varphi_n(\ell)=1+X_n(\ell)$ and solve for $X_n(\ell)$ in Theorem 14.
--
--   **Formalization Note** "$\varphi_n(\ell)$ exists over $K$" is stated as an element of the $F$-algebra whose coefficients in the diagram basis all lie in $K$; the conditions (i), (ii) over $F$ are equivalent to those over $K$ for such an element. No parity condition on $n-\ell$ is assumed here: the page states the claim for every $\ell<n$. The paper's diagrams are 1-based; Lean's are 0-based.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 8, §3, paragraph after Lemma 11

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, §3, p. 8: for `l < n` the splitting idempotent of `J_n(l)` exists
in `B_n` over `K`, i.e. with every diagram coefficient in `K`. -/
theorem existence (n l : ℕ) (hl : l < n) :
    ∃ φ : Br n, (∀ A : Diagram n, φ A ∈ Kring) ∧
      IsSplittingIdempotent (Jideal n l) φ := by sorry

end BrauerIdem.Splitting
