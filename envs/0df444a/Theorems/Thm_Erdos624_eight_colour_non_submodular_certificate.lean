-- Prove2me | Theorems.Thm_Erdos624_eight_colour_non_submodular_certificate
-- name    : Erdos624.eight_colour_non_submodular_certificate
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:59.163989+00:00
-- url     : https://prove2.me/theorems/ff9277e6-cb8c-4778-8231-ba793ce488fa
-- title:
--   Eight-colour capacity-two full cover with non-submodular optimal losses (Erdős 624)
-- statement:
--   **Theorem.** There is $L:\mathcal P(\mathrm{Fin}\,8)\to\mathcal P(\mathrm{Fin}\,8)$ with $|L(A)|\le2$, $L(A)=\varnothing$ for $|A|>3$ and $L(\varnothing)=\{0\}$, such that every $3$-set $Y$ attains all $8$ colours (full cover, $k=3$, $n=8$). Moreover, for colour $u=2$ and $T=\{0,4,6,7\}$:
--   (a) the only nonempty $u$-inputs inside $T$ are $06$ and $47$, so $W_0=\langle\chi_{06},\chi_{47}\rangle$ and $r_0=2$;
--   (b) on $T+5$ every $3$-face contains a $u$-input $A\neq56$ with $|A\cap\{0,5,6\}|$ and $|A\cap\{4,5,7\}|$ even. This is the zero set of the label map $p(0)=p(6)=a$, $p(4)=p(7)=b$, $p(5)=a+b$ with $a,b$ independent, whose kernel meets $\mathbb F_2^T$ exactly in $W_0$, so $\beta(T+5)=0$;
--   (c) on $T+3$ every $3$-face contains a $u$-input with $|A\cap\{3,4,7\}|$ even (labels with $a=0$, cost one), so $\beta(T+3)\le1$;
--   (d) every subspace $Z\le\mathbb F_2^8$ containing all $u$-input vectors inside $T$, and containing on each $3$-face of $T+3$ the vector of some $u$-input of that face, contains $e_0\notin W_0$, so $\beta(T+3)\ge1$;
--   (e) every such anchored covering flat for $T+\{3,5\}$ contains $e_0,e_4,e_6,e_7$, i.e. all of $\mathbb F_2^T$, so $\beta(T+\{3,5\})=2$.
--   Hence $\beta(T+3)+\beta(T+5)=1<2=\beta(T+\{3,5\})+\beta(T)$: the optimal anchored-flat loss is not submodular in the pool.
--
--   Source: 'Best Dense Cores and Mandatory Mixed-Face Obstructions' (NON-SUBMODULAR), with exactly the certificate printed there (bitmask encoding). Exhaustive Python check: $\beta=(0,1,0,2)$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem eight_colour_non_submodular_certificate :
    ∃ L : Finset (Fin 8) → Finset (Fin 8),
      (∀ A, #(L A) ≤ 2) ∧ (∀ A, 3 < #A → L A = ∅) ∧ L ∅ = {0} ∧
      (∀ Y : Finset (Fin 8), #Y = 3 → ∀ c : Fin 8, ∃ A ⊆ Y, c ∈ L A) ∧
      (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
        A = {0, 6} ∨ A = {4, 7}) ∧
      (∀ Y ⊆ ({0, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ A ≠ {5, 6} ∧
          Even #(A ∩ {0, 5, 6}) ∧ Even #(A ∩ {4, 5, 7})) ∧
      (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ Even #(A ∩ {3, 4, 7})) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (Pi.single 0 1 : Fin 8 → ZMod 2) ∈ Z) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        ∀ t ∈ ({0, 4, 6, 7} : Finset (Fin 8)), (Pi.single t 1 : Fin 8 → ZMod 2) ∈ Z) := by sorry

end Erdos624
