-- Prove2me | Theorems.Thm_DialARideBC_Valid_tight_tooth_path
-- name    : DialARideBC.Valid.tight_tooth_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:37.336115+00:00
-- url     : https://prove2.me/theorems/d05f6aae-93cf-403e-a8f8-c238d8d99cc8
-- title:
--   Proof of Proposition 5, p. 578 — a tight set T with i, n + i ∈ T is covered by one path that does not finish at i
-- statement:
--   Consider a DARP instance with $n$ users and a feasible solution with total arc flows $x_{ij}$. Let $i \in P$ be a user and $T \subseteq P \cup D$ a node set with $i \in T$ and $n+i \in T$. If
--   $$x(T) = |T| - 1,$$
--   then there is a path connecting all nodes of $T$: an ordering $w_1, \dots, w_r$ of the nodes of $T$, each listed exactly once, with $x_{w_s w_{s+1}} = 1$ for $s = 1,\dots,r-1$. Moreover this path does not finish at node $i$, i.e. $w_r \neq i$.
--
--   The last clause is where the precedence constraint of user $i$ enters the proof of Proposition 5: a path that ended at $i$ would visit $n+i$ before $i$.
--
--   **Formalization Note.** The path is a duplicate-free list `w` whose underlying set is $T$; "does not finish at $i$" is `w.getLast? ≠ some i`.
-- source:
--   Cordeau, A Branch-and-Cut Algorithm for the Dial-a-Ride Problem, Oper. Res. 54(3) (2006), p. 578, proof of Proposition 5, second and third sentences

import Mathlib
import Definitions.Def_DialARideBC_Valid_Model

namespace DialARideBC.Valid

theorem tight_tooth_path {n : ℕ} {K : Type} [Fintype K] (I : Instance n K) (s : Solution I)
    (i : ℕ) (hi : i ∈ P n) (T : Finset ℕ) (hT : T ⊆ PD n) (hiT : i ∈ T) (hniT : n + i ∈ T)
    (htight : xset s.x T = (T.card : ℝ) - 1) :
    ∃ w : List ℕ, w.Nodup ∧ w.toFinset = T ∧ (∀ a ∈ arcs w, s.x a.1 a.2 = 1) ∧
      w.getLast? ≠ some i := by sorry

end DialARideBC.Valid
