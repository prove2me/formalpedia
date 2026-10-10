-- Prove2me | Theorems.Thm_CircStability_Main_theorem_1_7
-- name    : CircStability.Main.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:20.884989+00:00
-- url     : https://prove2.me/theorems/79530ec2-1025-407e-a8c2-d60e9f19553c
-- title:
--   Theorem 1.7 — 2-connected, δ ≥ k, circumference 10 ≤ c ≤ n−1, e(G) > max{f(n,k+1,c), f(n,⌊c/2⌋−1,c)}: G ⊆ W_{n,k,c}, W_{n,⌊c/2⌋,c}, X∪Y or Z_{n,k,c}
-- statement:
--   Let $k\ge2$ and let $G$ be a 2-connected graph on $n$ vertices with minimum degree $\delta(G)\ge k$ and circumference $c$, where $10\le c\le n-1$. If
--
--   $$
--   e(G)>\max\big\{f(n,k+1,c),\ f\big(n,\lfloor c/2\rfloor-1,c\big)\big\},
--   $$
--
--   then one of the following holds:
--   1. $G\subseteq W_{n,k,c}$;
--   2. $G\subseteq W_{n,\lfloor c/2\rfloor,c}$;
--   3. $k=2$, $c$ is odd, and $G$ is a subgraph of a member of $\mathcal X_{n,c}\cup\mathcal Y_{n,c}$;
--   4. $k\ge3$ and $G\subseteq Z_{n,k,c}$.
--
--   Here $f(n,k,c)=\binom{c-k+1}{2}+k(n-c+k-1)$ is the number of edges of $W_{n,k,c}$. Woodall's conjecture (1976), which a modification of Kopylov's 1977 proof settles, bounds the edges of such a graph by $\max\{f(n,k,c),f(n,\lfloor c/2\rfloor,c)\}$. The theorem is a stability version of that bound: a graph within one step of the extremal threshold in either parameter is a subgraph of one of a few explicit graphs. For $k=2$ it is the stability theorem of Füredi, Kostochka, Luo and Verstraëte.
--
--   **Formalization Note.** "$G\subseteq H$" is an embedding of $G$ into $H$ (Mathlib's `⊑`). "Circumference $c$" means some cycle has length $c$ and no cycle is longer. The alternatives "(c) if $k=2$ and $c$ is odd, then …" and "(d) if $k\ge3$, then …" of the page are encoded as conjunctions; as implications they would make the theorem vacuous. Alternative 4 carries the divisibility $(k-1)\mid n-(c-k+1)$, without which $Z_{n,k,c}$ does not exist. The hypothesis $k\ge2$ is added: as printed the theorem fails at $k=1$. A member of $\mathcal X_{18,11}$ with $|X|=2$ is 2-connected, has circumference $11$, minimum degree $2$ and $69>68$ edges, yet lies in neither $W_{18,1,11}$ nor $W_{18,5,11}$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 4, Theorem 1.7 (footnote 5 not included)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

namespace CircStability.Main

theorem theorem_1_7 (n k c : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hδ : ∀ v, k ≤ G.degree v) (hcirc : HasCircumference G c)
    (hc : 10 ≤ c) (hcn : c ≤ n - 1)
    (hE : max (fNum n (k + 1) c) (fNum n (c / 2 - 1) c) < #G.edgeFinset) :
    G ⊑ wGraph n k c ∨ G ⊑ wGraph n (c / 2) c ∨
      (k = 2 ∧ Odd c ∧ ∃ H : SimpleGraph (Fin n), (IsXMember n c H ∨ IsYMember n c H) ∧ G ≤ H) ∨
      (3 ≤ k ∧ (k - 1) ∣ (n - (c - k + 1)) ∧ G ⊑ zGraph n k c) := by sorry

end CircStability.Main
