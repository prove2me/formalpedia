-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_delta_pow_expansion
-- name    : DirectedOpinion.NoMemory.delta_pow_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:24.869484+00:00
-- url     : https://prove2.me/theorems/11a2d0be-d502-4bb2-905c-4957126e8c68
-- title:
--   Proof of Proposition 3, p. 29 — Δ^s f(i) = Σ_{l≤s} Σ_{|j|=l} (Π_(i,j)/Π_i) a_{l,s} f((i,j))
-- statement:
--   Let a rooted tree be given in Ulam–Harris form, with in-degrees $n(\mathbf i)$ and weights $w(\mathbf i,j)$ on the edges from $\mathbf i$ to its children, and let $\lambda\in\mathbb R$. Let $\Delta$ be the operator
--   $$\Delta f(\mathbf i)=\sum_{j=1}^{n(\mathbf i)}w(\mathbf i,j)\,f((\mathbf i,j))+\lambda f(\mathbf i).$$
--   Then for every function $f$ on the labels, every node $\mathbf i$ and every $s\ge0$,
--   $$\Delta^s f(\mathbf i)=\sum_{l=0}^{s}\sum_{|\mathbf j|=l}\frac{\Pi_{(\mathbf i,\mathbf j)}}{\Pi_{\mathbf i}}\binom{s}{l}\lambda^{s-l}\,f((\mathbf i,\mathbf j)),$$
--   where the inner sum runs over the descendants of $\mathbf i$ at relative depth $l$ and $\Pi_{(\mathbf i,\mathbf j)}/\Pi_{\mathbf i}$ is the product of the weights along the path from $\mathbf i$ to $(\mathbf i,\mathbf j)$.
--
--   With $\lambda=1-c-d$ the coefficient $\binom{s}{l}\lambda^{s-l}$ is the paper's $a_{l,s}$, and this is the identity that the proof of Proposition 3 establishes by induction on $s$. It expresses the $s$-th power of the averaging operator as a weighted sum over the first $s$ generations of the subtree below $\mathbf i$.
--
--   **Formalization Note.** The statement holds for every tree, every real weight array and every $\lambda$; the page states it for the opinion recursion ($\lambda=1-c-d$), so this is a disclosed generalization. The ratio $\Pi_{(\mathbf i,\mathbf j)}/\Pi_{\mathbf i}$ is the relative path weight `pathW`, a product with no division, so a zero weight above $\mathbf i$ causes no $0/0$. Child indices are 0-based. In Lean $\lambda^0=1$ also for $\lambda=0$, as $a_{s,s}=1$ requires.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 29, proof of Proposition 3, first display

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Proof of Proposition 3, p. 29: Δ^s f(i) = Σ_{l=0}^s Σ_{|j|=l} (Π_(i,j)/Π_i) a_{l,s} f((i,j)),
for every tree in Ulam–Harris form, every weight array and every self-weight `lam`
(the page's a_{l,s} is the case `lam = 1 - c - d`). -/
theorem delta_pow_expansion (n : Label → ℕ) (w : Label → ℕ → ℝ) (lam : ℝ) (f : Label → ℝ)
    (i : Label) (s : ℕ) :
    (treeOp n w lam)^[s] f i =
      ∑ l ∈ Finset.range (s + 1), ∑ t ∈ level n i l,
        pathW n w i t * ((s.choose l : ℝ) * lam ^ (s - l)) * f (i ++ t) := by sorry

end DirectedOpinion.NoMemory
