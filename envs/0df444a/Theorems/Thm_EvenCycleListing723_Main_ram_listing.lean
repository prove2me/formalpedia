-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_ram_listing
-- name    : EvenCycleListing723.Main.ram_listing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T05:41:44.446048+00:00
-- url     : https://prove2.me/theorems/9005f909-3707-5a85-94e3-de11151531e8
-- title:
--   Counted word-RAM listing of all $2k$-cycles in $\tilde O_k(n^2+t+W_k(G))$
-- statement:
--   Fix an integer $k\ge 2$. There is a finite program $P$ for the mission's counted word RAM and constants $C,b>0$ and $q\ge 0$, chosen before the input, such that for every $n$, every simple graph $G$ on $\{0,\dots,n-1\}$ and every word width $w\ge b\,\ell(n)$, the program run on the input ($n$ followed by the adjacency matrix) halts after $T$ steps, having written exactly one canonical vertex list for each $2k$-cycle copy of $G$ (preceded by their number), with
--
--   $$T\le C\,\bigl(1+n^2+t_{2k}(G)+W_k(G)\bigr)\,\ell(n)^{q},\qquad \ell(n)=1+\lfloor\log_2\max(2,n)\rfloor .$$
--
--   Here $t_{2k}(G)$ is the number of $2k$-cycle copies and $W_k(G)$ is the exploration cost of the max-degree BFS rounds (the mission's `exploration`).
--
--   This is the running-time statement of Lemma 3.1 (deterministic version) in the form needed for Theorem 1.1: the listing algorithm of Section 3 (max-degree rounds, BFS to depth $k$, color coding with an explicitly constructed perfect family of colorings, backward pruning and depth-first listing, duplicate removal) runs within the stated time on an actual halting execution.
--
--   **Formalization Note** Execution, output format, `requiredWidth`, `softBudget` and `exploration` are the mission's definitions; no particular internal procedure or family size is prescribed.
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf, pp.4-5, Lemma 3.1 (deterministic clause, running time), as used in the proof of Theorem 1.1 p.8

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_Execution

set_option autoImplicit false

namespace EvenCycleListing723.Main

theorem ram_listing (k : ℕ) (hk : 2 ≤ k) :
    ∃ (P : Program) (C b q : ℕ), 0 < C ∧ 0 < b ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ), requiredWidth b n ≤ W →
        ∃ t : ℕ, haltsListing P k G W t ∧
          t ≤ softBudget C q n (n ^ 2 + cycleCount G k + exploration G k) := by sorry

end EvenCycleListing723.Main
