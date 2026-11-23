-- Prove2me | Theorems.Thm_Complexity_FiniteGame_PolyGame_inPSPACE
-- name    : Complexity.FiniteGame.PolyGame.inPSPACE
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:39:51.440007+00:00
-- url     : https://prove2.me/theorems/9ebe7b63-abca-4f7c-8ddd-76f15f1e4e8d
-- title:
--   Depth-first evaluation of a polynomially presented finite game uses polynomial space
-- statement:
--   Let $G$ be a polynomially presented finite impartial game, with instance encoding $\operatorname{enc}$, initial position $s_0(a)$, and normal-play winning predicate $W$. Then
--   $$
--   \{\,a : W(a,s_0(a))\,\}\in\mathsf{PSPACE}.
--   $$
--   More precisely, in the published multi-stack machine model, there is one machine which halts on every instance, outputs the bit $[W(a,s_0(a))]$, and whose total stack length in every reachable configuration is bounded by a polynomial in $|\operatorname{enc}(a)|$.
--
--   The proof uses depth-first search. At each node it enumerates the legal successors with the supplied polynomial-time move generator and reuses space after returning from a recursive call. Only the current branch and its unprocessed successor lists are stored. Polynomial bounds on position size and depth therefore give a polynomial space bound; no polynomial bound on running time is needed.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), p.5, proof of Theorem 1, first paragraph: DFS of the game tree while retaining only positions from the root to the current position. Generalized to the published `Complexity.FiniteGame.PolyGame` interface.

import Definitions.Def_Complexity_FiniteGame_PolyGame

open OptimalQueuingComplexity.Restless

theorem Complexity.FiniteGame.PolyGame.inPSPACE {α : Type} (G : PolyGame α) :
    InPSPACE G.enc (fun a => G.wins a (G.start a)) := by sorry
