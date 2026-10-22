-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_lemma_11
-- name    : BrauerIdem.Splitting.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:05.693738+00:00
-- url     : https://prove2.me/theorems/31a8dcae-378b-4417-834a-2f215845d846
-- title:
--   Lemma 11, p. 8 — the 𝔖_n-orbit sums D_t of diagrams form a basis of the centralizer Z_{𝔖_n}(B_n)
-- statement:
--   Let $B_n$ be the Brauer algebra over $F=\mathbb Q(\delta)$ with basis the set $\mathbf J_n$ of Brauer diagrams. The symmetric group $\mathfrak S_n$ acts on $\mathbf J_n$ by conjugation $A\mapsto\sigma A\sigma^{-1}$, which relabels every node $x,x'$ as $\sigma x,\sigma x'$. For an orbit $O$ write
--
--   $$
--   D_O=\sum_{B\in O}B
--   $$
--
--   for its orbit sum (the paper's $D_{\mathfrak t}=(A_{\mathfrak t})_\Sigma$, where $A_{\mathfrak t}$ is any diagram in the orbit). Let $Z_{\mathfrak S_n}(B_n)$ be the set of $x\in B_n$ commuting with every element of $\mathbf J_n[n]$, the diagrams with $n$ propagating lines (these span the copy of the group algebra of $\mathfrak S_n$ in $B_n$).
--
--   Then the orbit sums $\{D_O\}$, one for each $\mathfrak S_n$-orbit, are linearly independent, and
--
--   $$
--   Z_{\mathfrak S_n}(B_n)=\operatorname{span}\{D_O\}.
--   $$
--
--   This gives the basis in which the paper expands the central element $X_n(\ell)$ before solving for its coefficients.
--
--   **Formalization Note** The paper indexes the orbit sums by the image of the Spore function; by its Proposition 8 the orbits and these Spore classes are in bijection, and the Lean indexes by the orbits directly. The paper's basis is over $K$; the Lean states the basis property over $F$, the extension of scalars of the $K$-statement (the orbit sums have coefficients $0,1$). The orbit sums are of unnormalised diagrams.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 8, Lemma 11

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, Lemma 11, p. 8: the `𝔖_n`-orbit sums of diagrams form a basis of
the centralizer of `K𝔖_n` (the span of the diagrams with `n` propagating lines). -/
theorem lemma_11 (n : ℕ) :
    LinearIndependent F (fun O : Orbit n => orbitSum O) ∧
    ∀ x : Br n,
      (∀ A : Diagram n, propCount A = n → bmul (basis A) x = bmul x (basis A)) ↔
        x ∈ Submodule.span F (Set.range (fun O : Orbit n => orbitSum O)) := by sorry

end BrauerIdem.Splitting
