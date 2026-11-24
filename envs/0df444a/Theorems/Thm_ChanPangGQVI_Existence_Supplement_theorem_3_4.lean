-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_Supplement_theorem_3_4
-- name    : ChanPangGQVI.Existence.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:55:52.66627+00:00
-- url     : https://prove2.me/theorems/90c25939-1d84-422b-a194-3dfacb510efa
-- title:
--   Theorem 3.4 — existence of an equilibrium point of an abstract economy with quasi-concave aggregate utility ψ
-- statement:
--   Let $\{(X^j,S^j,u^j)\}_{j\in N}$ be an abstract economy: $N$ is a finite set of individuals, $X^j\subseteq\mathbb R^{n_j}$ is the strategy set of $j$, $X=\prod_{j\in N}X^j$, $u^j:X\times X^j\to\mathbb R$ is the utility of $j$ and $S^j:X\to X^j$ is its feasibility correspondence. Assume that for each $j\in N$:
--
--   1. $X^j$ is a nonempty compact convex subset of $\mathbb R^{n_j}$;
--   2. $S^j$ is a nonempty, closed and convex valued, continuous (upper and lower semicontinuous) point-to-set mapping on $X$;
--   3. $u^j$ is continuous on $X\times X^j$;
--   4. the function
--   $$
--   \psi(y,x)=\sum_{j\in N}u^j(x,y_j)
--   $$
--   is quasi-concave in $y\in X$ for each fixed $x\in X$.
--
--   Then the economy has an equilibrium point: there is $x^*\in X$ such that for every $j\in N$, $x^*_j\in S^j(x^*)$ and
--
--   $$
--   u^j(x^*,x^*_j)=\max\{\,u^j(x^*,\xi_j):\xi_j\in S^j(x^*)\,\}.
--   $$
--
--   This is a finite-dimensional existence theorem of Debreu type. Its hypothesis 4 is on the sum $\psi$, not on each $u^j$ separately; the paper remarks that Debreu's per-individual quasi-concavity of $u^j(x,y_j)$ in $y_j$ does not imply it, while concavity of each $u^j$ in its own strategy does.
--
--   **Formalization Note** Profiles live in the product $\prod_j\mathbb R^{n_j}$ with the product topology; $S^j$ and $u^j$ are total functions whose values off $X$ (resp. $X\times X^j$) never enter. Semicontinuity of $S^j$ is relative to $X$; continuity of $u^j$ is relative to $X\times X^j$. Closed values of $S^j$ are Berge's convention for upper semicontinuous mappings (compact values; $S^j(x)$ lies in the compact $X^j$).
--
--   Differences from the source:
--   - reading: S^j upper semicontinuous (Berge) → in addition S^j(x) closed for x ∈ X; reason: Berge's upper semicontinuous mappings have compact values; without it the theorem fails (X^1 = [0, 1], S^1 ≡ (0, 1), u^1(x, y) = y has no maximiser over S^1(x)).
--   - reading: "u^j(x*, x*_j) = max{u^j(x*, ξ_j) : ξ_j ∈ S^j(x*)}" → x*_j ∈ S^j(x*) and u^j(x*, ξ) ≤ u^j(x*, x*_j) for all ξ ∈ S^j(x*); reason: Debreu's definition [7], which the paper recalls, and what the proof produces (x* ∈ K(x*) = ∏ S^j(x*)); it implies the literal equality.
--   - encoding: S^j : X → X^j, u^j : X × X^j → ℝ, continuity on X → total functions with S^j(x) ⊆ X^j for x ∈ X and continuity and hemicontinuity relative to X (resp. X × X^j); reason: values off the domain are irrelevant; same instances.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 217, Theorem 3.4

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_Supplement_AbstractEconomy

namespace ChanPangGQVI.Existence.Supplement

/-- Chan and Pang 1982, p. 217, Theorem 3.4. Given an abstract economy `{(X^j, S^j, u^j)}_{j ∈ N}`
(`N` finite) which satisfies, for each `j ∈ N`:
(i) `X^j` is a nonempty compact convex subset of `ℝ^{n_j}`;
(ii) `S^j : X → X^j` is a nonempty continuous convex-valued point-to-set mapping;
(iii) `u^j : X × X^j → ℝ` is continuous;
(iv) the function `ψ(y, x) = ∑_{j ∈ N} u^j(x, y_j)` is quasi-concave in `y ∈ X` for each fixed
`x ∈ X`.
Then there exists an equilibrium.

Implicit hypothesis made explicit: each `S^j(x)`, `x ∈ X`, is closed (`hS_closed`, Berge's
compact values; it is a subset of the compact `X^j`). "Continuous" for `S^j` is upper and lower
hemicontinuity relative to `X`; continuity of `u^j` is relative to `X × X^j`. Profiles carry the
product topology. -/
theorem theorem_3_4 {N : Type*} [Fintype N] {d : N → ℕ} (G : AbstractEconomy N d)
    (hX_ne : ∀ j, (G.X j).Nonempty) (hX_cpt : ∀ j, IsCompact (G.X j))
    (hX_conv : ∀ j, Convex ℝ (G.X j))
    (hS_ne : ∀ j, ∀ x ∈ G.profiles, (G.S j x).Nonempty)
    (hS_usc : ∀ j, UpperHemicontinuousOn (G.S j) G.profiles)
    (hS_lsc : ∀ j, LowerHemicontinuousOn (G.S j) G.profiles)
    (hS_conv : ∀ j, ∀ x ∈ G.profiles, Convex ℝ (G.S j x))
    (hS_closed : ∀ j, ∀ x ∈ G.profiles, IsClosed (G.S j x))
    (hu : ∀ j, ContinuousOn (fun p : Profile d × EuclideanSpace ℝ (Fin (d j)) => G.u j p.1 p.2)
      (G.profiles ×ˢ G.X j))
    (hψ : ∀ x ∈ G.profiles, QuasiconcaveOn ℝ G.profiles (fun y => ∑ j, G.u j x (y j))) :
    ∃ x : Profile d, G.IsEquilibriumPoint x := by sorry

end ChanPangGQVI.Existence.Supplement
