-- Prove2me | Theorems.Thm_BellmanDP_Games_game_equation_exists_unique
-- name    : BellmanDP.Games.game_equation_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T21:16:35.412986+00:00
-- url     : https://prove2.me/theorems/5d277973-9ca9-46ec-8124-eaf441eb7bb7
-- title:
--   Chapter X, Theorem 1 — existence and uniqueness for the multi-stage game equation
-- statement:
--   Consider the general multi-stage game of Chapter X, § 12, under the hypotheses (4a)–(4e): continuity of $R$, $h$, $T$, $T'$; choice domains $S(P,P')$, $S'(P,P')$ varying continuously; the shrinking condition $\|T\|+\|T'\|\le k(\|P\|+\|P'\|)$ with $k<1$; $\sum_{n\ge1}w(k^nc)<\infty$ for all $c>0$; and $|h|\le 1$. Then the equation
--   $$f(P,P')=\max_{G}\min_{G'}\iint_{u\in S,\,v\in S'}\big[R(u,v)+h(P,P';u,v)f(T,T')\big]\,dG(u)\,dG'(v)=\min_{G'}\max_{G}\big[\ \cdots\ \big]$$
--   has a unique solution in the class of functions that are continuous for all $P\in D$, $P'\in D'$ and vanish when $P$ and $P'$ are both null vectors. Moreover the successive approximations
--   $$f_0(P,P')=\max_G\min_{G'}\iint R(u,v)\,dG(u)\,dG'(v)=\min_{G'}\max_G[\ \cdots\ ],$$
--   $$f_{N+1}(P,P')=\max_G\min_{G'}T(P,P';f_N;G,G')=\min_{G'}\max_G T(P,P';f_N;G,G'),\qquad N\ge 0,$$
--   are well defined (each one-stage game has a value), and $f_N\to f$ uniformly in every bounded region $\|P\|+\|P'\|\le c$.
--
--   This is the chapter's central existence and uniqueness theorem. It justifies describing the infinite multi-stage game by the functional equation.
--
--   **Formalization Note** The statement asserts: a solution $f$ in the class exists; any solution $F$ in the class agrees with $f$ on $D\times D'$; some sequence satisfying the recurrence (with each one-stage value attained) exists; and every such sequence converges to $f$ uniformly on each region $\{P\in D,\ P'\in D' : \|P\|+\|P'\|\le c\}$. Values outside $D\times D'$ play no role.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 12, Theorem 1, pp. 296-297

import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 1, pp. 296–297. Under hypotheses (4a)–(4e)
(`GameHyp g k`), the equation (12.2)
`f(P, P') = Max_G Min_{G'} ∫∫ [R(u, v) + h(P, P'; u, v) f(T, T')] dG(u) dG'(v) = Min_{G'} Max_G [⋯]`
has a unique solution in the class of functions continuous for all `P ∈ D`, `P' ∈ D'` and
vanishing at `P = 0, P' = 0`. It is the limit of the successive approximations (12.5)
`f₀(P, P') = Max_G Min_{G'} ∫∫ R(u, v) dG dG' = Min_{G'} Max_G [⋯]`,
`f_{N+1}(P, P') = Max_G Min_{G'} T(P, P'; f_N; G, G') = Min_{G'} Max_G T(P, P'; f_N; G, G')`,
which are all defined, and the convergence is uniform in every bounded region of `(P, P')`
space. -/
theorem game_equation_exists_unique {n n' m m' : ℕ} (g : GameData n n' m m') (k : ℝ)
    (hg : GameHyp g k) :
    ∃ f : Vec n → Vec n' → ℝ, InSolutionClass g f ∧ IsGameSolution g f ∧
      (∀ F : Vec n → Vec n' → ℝ, InSolutionClass g F → IsGameSolution g F →
        ∀ P ∈ g.D, ∀ P' ∈ g.D', F P P' = f P P') ∧
      (∃ fs : ℕ → Vec n → Vec n' → ℝ,
        (∀ P ∈ g.D, ∀ P' ∈ g.D', ValueAt g g.R P P' (fs 0 P P')) ∧ IsIterSeq g fs) ∧
      ∀ fs : ℕ → Vec n → Vec n' → ℝ,
        (∀ P ∈ g.D, ∀ P' ∈ g.D', ValueAt g g.R P P' (fs 0 P P')) → IsIterSeq g fs →
        ∀ c : ℝ, TendstoUniformlyOn (fun N (z : Vec n × Vec n') => fs N z.1 z.2)
          (fun z => f z.1 z.2) Filter.atTop (region g c) := by sorry

end BellmanDP.Games
