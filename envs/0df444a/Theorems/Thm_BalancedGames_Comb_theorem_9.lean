-- Prove2me | Theorems.Thm_BalancedGames_Comb_theorem_9
-- name    : BalancedGames.Comb.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:26.814175+00:00
-- url     : https://prove2.me/theorems/5a6d862c-0cf3-4e3d-988a-2d9bb6a866b0
-- title:
--   Theorem 9, p. 12 — a family 𝒟 ⊆ 2^N ∖ {∅, N} defines a vertex of BG+(n) iff 𝒟 = ∅ or ⋂𝒟 ≠ ∅
-- statement:
--   Let $n\ge1$ and let $\mathcal D$ be a family of coalitions with $\varnothing\neq S\neq N$ for every $S\in\mathcal D$. Let $v_{\mathcal D}$ be the game with $v_{\mathcal D}(S)=1$ if $S\in\mathcal D$ or $S=N$, and $v_{\mathcal D}(S)=0$ otherwise. Then
--
--   $$v_{\mathcal D}\ \text{is a vertex of } \mathcal{BG}_+(n) \iff \mathcal D=\varnothing \ \text{ or }\ \bigcap\mathcal D\neq\varnothing .$$
--
--   Together with Theorem 8 this lists the vertices of $\mathcal{BG}_+(n)$: they are the games $v_{\mathcal D}$ of the families with a common player, plus the unanimity game $u_N=v_\varnothing$.
--
--   **Formalization Note** $\bigcap\mathcal D\neq\varnothing$ (for $\mathcal D\neq\varnothing$) is written "some player $i$ belongs to every member of $\mathcal D$". The hypothesis $n\ge1$ is the paper's domain and is needed: at $n=0$ the polytope is empty while $\mathcal D=\varnothing$.
--
--   Differences from the source:
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves extreme points.
--   - encoding: balanced by (4) → nonempty core; reason: p. 4 identifies the two (Theorem 1).
--   - encoding: "$\mathcal D$ defines a vertex" → the game $v_{\mathcal D}$ (1 on $\mathcal D\cup\{N\}$, 0 elsewhere) is an extreme point; reason: p. 11–12, the game corresponding to $\mathcal D$.
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 12, Theorem 9

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Theorem 9** (p. 12). Let `𝒟` be a family of coalitions in `2^N ∖ {∅, N}`, `n ≥ 1`. The game
`v_𝒟` (`1` on `𝒟 ∪ {N}`, `0` elsewhere) is a vertex of `BG+(n)` iff `𝒟 = ∅` or `⋂𝒟 ≠ ∅`
(some player belongs to every member of `𝒟`). -/
theorem theorem_9 (n : ℕ) (hn : 1 ≤ n) (D : Finset (Finset (Fin n)))
    (hD : ∀ S ∈ D, S ≠ ∅ ∧ S ≠ Finset.univ) :
    gameOf D ∈ Set.extremePoints ℝ (BGplus n) ↔ D = ∅ ∨ ∃ i, ∀ S ∈ D, i ∈ S := by sorry

end BalancedGames.Comb
