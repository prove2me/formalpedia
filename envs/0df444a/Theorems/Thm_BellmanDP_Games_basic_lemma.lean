-- Prove2me | Theorems.Thm_BellmanDP_Games_basic_lemma
-- name    : BellmanDP.Games.basic_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:16:18.008107+00:00
-- url     : https://prove2.me/theorems/1a7c53a8-a181-4360-9c82-12e19afaea2c
-- title:
--   Chapter X, Lemma 1 — the basic lemma $|L(f)-L_1(F)|\le\max_{u,v}\,[\,|R-R_1|+|h|\,|f(T,T')-F(T,T')|\,]$
-- statement:
--   Fix a state $(P,P')$ of the multi-stage game, with choice domains $S=S(P,P')$ and $S'=S'(P,P')$. For two functions $f,F$ of the state and two single-stage returns $R,R_1$, let
--   $$L(f)=\max_G\min_{G'}\iint_{u\in S,\,v\in S'}\big[R(u,v)+h(P,P';u,v)f(T,T')\big]\,dG(u)\,dG'(v)=\min_{G'}\max_G[\ \cdots\ ],$$
--   $$L_1(F)=\max_G\min_{G'}\iint_{u\in S,\,v\in S'}\big[R_1(u,v)+h(P,P';u,v)F(T,T')\big]\,dG(u)\,dG'(v)=\min_{G'}\max_G[\ \cdots\ ],$$
--   where $G$, $G'$ range over mixed strategies on $S$, $S'$. That max-min equals min-max for each of the two one-stage games is a hypothesis, as in Bellman's footnote. Then
--   $$|L(f)-L_1(F)|\le\max_{u\in S}\max_{v\in S'}\Big[\,|R(u,v)-R_1(u,v)|+|h(P,P';u,v)|\,\big|f(T,T')-F(T,T')\big|\,\Big].$$
--
--   The lemma says the value of a one-stage game moves by at most the largest change of its kernel. Bellman uses it for existence, uniqueness, convergence of successive approximations and stability of the multi-stage game equation.
--
--   **Formalization Note** The conclusion is stated as $|L-L_1|\le M$ for every upper bound $M$ of the bracket on $S\times S'$, which is equivalent to the bound by its maximum. The two kernels are assumed measurable and bounded on $S\times S'$ so that the integrals are defined; Bellman leaves this implicit. The hypotheses that each game has a value are `ValueAt` statements with all extrema attained.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 11, Lemma 1 and footnote 4, p. 294

import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Lemma 1, p. 294 (the basic lemma). Fix a state
`(P, P')`. Let `L = L(f)` be the value of the one-stage game with kernel
`R(u, v) + h(P, P'; u, v) f(T, T')` and `L₁ = L₁(F)` the value of the game with kernel
`R₁(u, v) + h(P, P'; u, v) F(T, T')`, both played with mixed strategies on the choice domains
`S = S(P, P')`, `S' = S'(P, P')`; that each game has a value (max-min = min-max) is a
hypothesis, as in the book's footnote 4. Then
`|L(f) − L₁(F)| ≤ Max_{u ∈ S} Max_{v ∈ S'} [|R(u, v) − R₁(u, v)| + |h(P, P'; u, v)| |f(T, T') − F(T, T')|]`,
stated as `|L − L₁| ≤ M` for every upper bound `M` of the bracket on `S × S'`. The two kernels
are assumed measurable and bounded on `S × S'`, so that the integrals exist. -/
theorem basic_lemma {n n' m m' : ℕ} (g : GameData n n' m m') (R₁ : Vec m → Vec m' → ℝ)
    (f F : Vec n → Vec n' → ℝ) (P : Vec n) (P' : Vec n') (L L₁ : ℝ)
    (hmeas : Measurable (fun z : Vec m × Vec m' => stageKernel g f P P' z.1 z.2))
    (hmeas₁ : Measurable (fun z : Vec m × Vec m' => stageKernel { g with R := R₁ } F P P' z.1 z.2))
    (hbdd : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel g f P P' u v| ≤ C)
    (hbdd₁ : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel { g with R := R₁ } F P P' u v| ≤ C)
    (hL : ValueAt g (stageKernel g f P P') P P' L)
    (hL₁ : ValueAt g (stageKernel { g with R := R₁ } F P P') P P' L₁)
    (M : ℝ)
    (hM : ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |g.R u v - R₁ u v| + |g.h P P' u v| *
        |f (g.T P P' u v) (g.T' P P' u v) - F (g.T P P' u v) (g.T' P P' u v)| ≤ M) :
    |L - L₁| ≤ M := by sorry

end BellmanDP.Games
