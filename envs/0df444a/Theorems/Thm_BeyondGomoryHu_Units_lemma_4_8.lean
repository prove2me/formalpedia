-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_4_8
-- name    : BeyondGomoryHu.Units.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:02.863101+00:00
-- url     : https://prove2.me/theorems/32ec71f0-721b-4878-acc1-c54aa9b55d52
-- title:
--   Lemma 4.8 — the case x or y outside LCA_T(w,z) (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   In the conditions of Lemma 4.6 ($T$ tied to $v$, $M$ the maximizer of $\mathcal C_{T,v}$, a $(w,z)$-mincut with $w,z\in\alpha$), let $x,y\in\alpha$. If $z$ and $T$ are in different $x,y$-units and
--   $$\lambda_{w,z}>\min\{\lambda_{x,z},\lambda_{y,z}\},$$
--   then $v$ and $T$ are in different $x,y$-units.
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 4.8, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_4_8 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a : N) (ha : (K.terms a).Nonempty) (T : Set N) (hT : IsAlphaComp K a T) (v : V)
    (hv : Tied K T v) (M : Finset V) (hM : IsMaximizer G K a T v M) (w z : V)
    (hw : w ∈ K.terms a) (hz : z ∈ K.terms a) (hwz : IsOrientedMincut G w z M) (x y : V)
    (hx : x ∈ K.terms a) (hy : y ∈ K.terms a)
    (hzT : ¬ SameUnitSets G x y {z} (compTerms K T))
    (hlt : min (lam G {x, z}) (lam G {y, z}) < lam G {w, z}) :
    ¬ SameUnitSets G x y {v} (compTerms K T) := by sorry

end BeyondGomoryHu.Units
