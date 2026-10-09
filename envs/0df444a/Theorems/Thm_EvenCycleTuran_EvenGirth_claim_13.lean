-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_claim_13
-- name    : EvenCycleTuran.EvenGirth.claim_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:38.757847+00:00
-- url     : https://prove2.me/theorems/511e6124-8c6e-4fc1-9381-8464cc3d51b5
-- title:
--   Claim 13, p. 20 — a fat pair is joined by a path of length l whose interior avoids any given set of at most 4l vertices
-- statement:
--   Let $l\ge2$ and let $G$ be a finite graph with no cycle of length $3,\dots,2l-1$. Let $\{u,v\}$ be a fat pair, i.e. there are at least $4l^2$ paths of length $l$ between $u$ and $v$, and let $X$ be a set of at most $4l$ vertices. Then there is a path $P$ of length $l$ between $u$ and $v$ with
--   $$\big(V(P)\setminus\{u,v\}\big)\cap X=\emptyset .$$
--
--   The claim lets the proof of Claim 14 route a fresh path of length $l$ between opposite vertices of a fat cycle, avoiding all previously used vertices.
--
--   **Formalization Note.** The path is an injective sequence $q_0=u,\dots,q_l=v$ of consecutively adjacent vertices, and only $q_0$, $q_l$ may lie in $X$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 20, Claim 13 (standing hypothesis "G has girth at least 2l", p. 20)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem claim_13 {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (hl : 2 ≤ l)
    (hG : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1)) G)
    (u v : V) (huv : IsFatPair G l u v) (X : Finset V) (hX : #X ≤ 4 * l) :
    ∃ q : Fin (l + 1) → V, IsPathOfLength G l u v q ∧
      ∀ i : Fin (l + 1), q i ∈ X → i = 0 ∨ i = Fin.last l := by sorry

end EvenCycleTuran.EvenGirth
