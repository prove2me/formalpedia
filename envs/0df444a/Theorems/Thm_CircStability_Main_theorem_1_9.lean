-- Prove2me | Theorems.Thm_CircStability_Main_theorem_1_9
-- name    : CircStability.Main.theorem_1_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:44.527255+00:00
-- url     : https://prove2.me/theorems/8bbfe83e-654f-4436-a192-8217be6b182a
-- title:
--   Theorem 1.9 — with C a longest cycle: Ḡ = W_{n,k,c}, G ⊆ W_{n,⌊c/2⌋,c}, (k = 2, c odd) G in X∪Y, or (k ≥ 3) Ḡ = Z_{n,k,c}
-- statement:
--   Let $k\ge2$, let $G$ be a 2-connected graph on $n$ vertices with $\delta(G)\ge k$, and let $C$ be a longest cycle of $G$ of length $c\in[10,n-1]$. If
--
--   $$
--   e(G)>\max\big\{f(n,k+1,c),\ f(n,\lfloor c/2\rfloor-1,c)\big\},
--   $$
--
--   then one of the following holds, where $\overline G$ is the $C$-closure of $G$:
--   1. $\overline G=W_{n,k,c}$;
--   2. $G\subseteq W_{n,\lfloor c/2\rfloor,c}$;
--   3. $k=2$, $c$ is odd, and $G$ is a subgraph of a member of $\mathcal X_{n,c}\cup\mathcal Y_{n,c}$;
--   4. $k\ge3$ and $\overline G=Z_{n,k,c}$.
--
--   Theorem 1.9 refines the main Theorem 1.7 by describing the extremal graphs exactly through the $C$-closure; Theorem 1.7 follows from it because $G\subseteq\overline G$.
--
--   **Formalization Note.** Alternatives 1 and 4 are isomorphisms of $\overline G$; alternative 2 is an embedding of $G$ (not $\overline G$). The page's alternatives "(c) if $k=2$ and $c$ is odd, then …" and "(d) if $k\ge3$, then …" are encoded as conjunctions; read as implications they would make the theorem trivial. Alternative 4 carries the divisibility $(k-1)\mid n-(c-k+1)$, without which $Z_{n,k,c}$ does not exist. The hypothesis $k\ge2$ is added: as printed ("$\delta(G)\ge k$" for every $k$) the theorem fails at $k=1$. A member of $\mathcal X_{18,11}$ with $|X|=2$ is 2-connected, has circumference $11$, minimum degree $2$ and $69>68=\max\{f(18,2,11),f(18,4,11)\}$ edges, yet lies in neither $W_{18,1,11}$ nor $W_{18,5,11}$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 4, Theorem 1.9 (proof p. 5, §1.7)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem theorem_1_9 (n k c : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hδ : ∀ v, k ≤ G.degree v) {u : Fin n} (C : G.Walk u u)
    (hC : IsLongestCycle G C) (hlen : C.length = c) (hc : 10 ≤ c) (hcn : c ≤ n - 1)
    (hE : max (fNum n (k + 1) c) (fNum n (c / 2 - 1) c) < #G.edgeFinset) :
    Nonempty (cClosure G C.support.toFinset ≃g wGraph n k c) ∨
      G ⊑ wGraph n (c / 2) c ∨
      (k = 2 ∧ Odd c ∧ ∃ H : SimpleGraph (Fin n), (IsXMember n c H ∨ IsYMember n c H) ∧ G ≤ H) ∨
      (3 ≤ k ∧ (k - 1) ∣ (n - (c - k + 1)) ∧
        Nonempty (cClosure G C.support.toFinset ≃g zGraph n k c)) := by sorry

end CircStability.Main
