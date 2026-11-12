-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_3_8
-- name    : BeyondGomoryHu.Units.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:58.965894+00:00
-- url     : https://prove2.me/theorems/6e0d7f38-ebde-4d3d-b21b-8d02eee9e819
-- title:
--   Lemma 3.8 — tied component dichotomy (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\alpha$ be a nonempty node of $H_\mu$ with $x,y\in\alpha$, and let $T$ be an $\alpha$-component tied to $v$. Exactly one of the following holds:
--   1. (Merged) one $x,y$-unit contains both $v$ and $T$;
--   2. (Split) the $x,y$-unit of $v$ contains no $u\in\mu$ and no $u$ that is not tied to $T$.
--   $$\text{Merged}\ \veebar\ \text{Split}.$$
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ a non-leaf node of T, α its child that is a nonempty node of H_µ with x, y ∈ α → µ a node of T with |µ| ≥ 2, carcass K of µ, a node a of H_µ with x, y ∈ terms(a); reason: the children of µ are the nonempty nodes of H_µ (Theorem 2.2); same instances
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 3.8 (Tied component dichotomy), p. 9 (PDF 11)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_3_8 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a : N) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms a) (T : Set N) (hT : IsAlphaComp K a T) (v : V)
    (hv : Tied K T v) :
    let merged := SameUnitSets G x y {v} (compTerms K T)
    let split := ∀ u, SameUnit G x y v u → u ∉ μ ∧ Tied K T u
    (merged ∨ split) ∧ ¬ (merged ∧ split) := by sorry

end BeyondGomoryHu.Units
