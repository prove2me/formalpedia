-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_observation_5_3
-- name    : BeyondGomoryHu.Units.observation_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:52.394078+00:00
-- url     : https://prove2.me/theorems/6b3f7619-cd1f-4e98-891d-a130fa8af55c
-- title:
--   Observation 5.3 — LCA_T(w,z) as a connectivity threshold set (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights and $\mathcal T$ its skeleton hierarchy. For all $w,z\in V$,
--   $$\mathrm{LCA}_{\mathcal T}(w,z)=\{v\in V\mid \lambda_{v,z}\ge\lambda_{w,z}\},$$
--   with $\lambda_{u,u}=\infty$ (so for $w=z$ both sides are $\{w\}$).
--
--   **Formalization Note.** `IsLCA G w z μ` says that $\mu$ is a node of $\mathcal T$ containing $w,z$ and contained in every such node.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Observation 5.3, p. 20 (PDF 22)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem observation_5_3 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (w z : V) (μ : Finset V)
    (hμ : IsLCA G w z μ) :
    (μ : Set V) = {v | lam G {w, z} ≤ lam G {v, z}} := by sorry

end BeyondGomoryHu.Units
