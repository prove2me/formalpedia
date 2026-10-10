-- Prove2me | Theorems.Thm_CircStability_Main_f_split
-- name    : CircStability.Main.f_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:15.411387+00:00
-- url     : https://prove2.me/theorems/aeda7620-8c76-4462-8838-e21b069a72f9
-- title:
--   §1.7, p. 5 — f(n, ⌊c/2⌋−1, c) = (⌊c/2⌋−1)(n−c) + h(c+1, ⌊c/2⌋−1), and the resulting split of the edges
-- statement:
--   Let $c\le n$ and $\kappa=\lfloor c/2\rfloor-1$. Then
--
--   $$
--   f(n,\kappa,c)=\kappa\,(n-c)+h(c+1,\kappa).
--   $$
--
--   Consequently, for every graph $G$ on $n$ vertices and every vertex set $S$ (in the paper $S=V(C)$ for a longest cycle $C$): if $e(G)>f(n,\kappa,c)$, then either more than $\kappa(n-c)$ edges of $G$ have at most one endpoint in $S$, or more than $h(c+1,\kappa)$ edges have both endpoints in $S$.
--
--   This is the reduction step in the proof of Theorem 1.9: the first alternative is handled by Theorem 1.12, the second by Theorem 1.13 (Theorem 4.1).
--
--   **Formalization Note.** Here $f(n,k,c)=\binom{c-k+1}{2}+k(n-c+k-1)$ and $h(n,k)=\binom{n-k}{2}+k(k-1)$ as in the Setting module, computed in $\mathbb N$; the hypothesis $c\le n$ makes the natural-number subtractions exact.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 5, §1.7, proof of Theorem 1.9 (first two sentences)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

namespace CircStability.Main

theorem f_split (n c : ℕ) (hcn : c ≤ n) :
    fNum n (c / 2 - 1) c = (c / 2 - 1) * (n - c) + hNum (c + 1) (c / 2 - 1) ∧
      ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], ∀ S : Finset (Fin n),
        fNum n (c / 2 - 1) c < #G.edgeFinset →
          (c / 2 - 1) * (n - c) < edgesOffCycle G S ∨ hNum (c + 1) (c / 2 - 1) < edgesOnCycle G S := by sorry

end CircStability.Main
