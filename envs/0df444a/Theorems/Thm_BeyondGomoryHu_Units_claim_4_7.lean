-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_claim_4_7
-- name    : BeyondGomoryHu.Units.claim_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:50:10.314431+00:00
-- url     : https://prove2.me/theorems/9e625260-fc33-4447-92c4-d5e4ff8918a9
-- title:
--   Claim 4.7 — pairs of larger connectivity are not separated (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights and $x,y,w,z\in V$. If
--   $$\min\{\lambda_{x,z},\lambda_{y,z}\}<\lambda_{w,z},$$
--   then no $x,y$-mincut separates $w$ and $z$. Here $\lambda_{u,u}=\infty$.
--
--   **Formalization Note.** $\lambda$ takes values in $\mathbb N\cup\{\infty\}$ (`lam`), with value $\infty$ when no cut exists.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Claim 4.7, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem claim_4_7 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (x y w z : V)
    (hlt : min (lam G {x, z}) (lam G {y, z}) < lam G {w, z}) :
    ∀ A : Finset V, IsMincut G {x, y} A → (w ∈ A ↔ z ∈ A) := by sorry

end BeyondGomoryHu.Units
