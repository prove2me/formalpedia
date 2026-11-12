-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_6_7
-- name    : BeyondGomoryHu.Units.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:14.628704+00:00
-- url     : https://prove2.me/theorems/585f03d7-a7b9-4548-a175-aa886b7ff2ce
-- title:
--   Lemma 6.7 — internal bucket order in the LCA (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$.
--
--   Let $\mu=\mathrm{LCA}_{\mathcal T}(x,y)$, $T_1,\dots,T_k$ a traversal list, and $u,v$ split vertices with the same rightmost component $T$. For $w\in\{u,v\}$ let $\gamma_w$ be the endpoint of $\pi_\mu(w)$ in $T$ (or, if $\pi_\mu(w)$ misses $T$, its endpoint at the entry node of the cycle whose first component is $T$), and $f_w$ the tree-edge of $\pi_\mu(w)$ at $\gamma_w$. With $\preceq=\preceq_{(x,y)}$:
--   1. if $f_u\notin\pi_\mu(v)$, then $u\not\preceq v$;
--   2. if $f=f_u=f_v$ and $\gamma=\gamma_u=\gamma_v$, then
--   $$\sigma_{f,\gamma}(u)<\sigma_{f,\gamma}(v)\ \Longrightarrow\ u\not\preceq v.$$
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs). $\sigma_{f,\gamma}$ ranges over every numbering with the properties of Lemma 6.3 (`IsSigma`).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ = LCA_T(x, y), with children α ∋ x and β ∋ y → a node µ of T with |µ| ≥ 2, a carcass K of µ, and nonempty nodes a ≠ b of H_µ with x ∈ α, y ∈ β; reason: the children of µ are exactly the nonempty nodes of H_µ (Theorem 2.2), so x and y lie in different children iff µ = LCA_T(x, y)
--   - generalization: u, v ∈ B, the bucket of the chosen split representatives of R0 placed next to T → any two split vertices whose rightmost component is T; reason: B consists of such vertices and the proof uses only this; R0 is an artefact of the paper's algorithm
--   - reading: σ_{f,γ}, "the" numbering of Lemma 6.3 → every numbering satisfying the two properties of Lemma 6.3; reason: Lemma 6.3 asserts existence only; the proof uses only its first property
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 6.7 (Internal bucket order in the LCA), p. 23 (PDF 25)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_6_7 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a b : N) (hab : a ≠ b) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms b) (L : List (Set N)) (hL : IsTraversalList K a b L)
    (T : Set N) (u v : V)
    (hu : ¬ ∃ T', IsABComp K a b T' ∧ projNodes K u ⊆ T')
    (hv : ¬ ∃ T', IsABComp K a b T' ∧ projNodes K v ⊆ T')
    (hru : IsRightmost K a b L u T) (hrv : IsRightmost K a b L v T)
    (γu γv : N) (fu fv : Sym2 N)
    (hγu : γu = (K.proj u).1 ∨ γu = (K.proj u).2) (hγv : γv = (K.proj v).1 ∨ γv = (K.proj v).2)
    (hγuT : ((projNodes K u ∩ T).Nonempty → γu ∈ T) ∧
      (¬ (projNodes K u ∩ T).Nonempty → γu ∈ Pnodes K a b ∧ IsEntryExit K a b γu))
    (hγvT : ((projNodes K v ∩ T).Nonempty → γv ∈ T) ∧
      (¬ (projNodes K v ∩ T).Nonempty → γv ∈ Pnodes K a b ∧ IsEntryExit K a b γv))
    (hfu : fu ∈ projEdges K u ∧ γu ∈ fu ∧ IsTreeEdge K.H fu)
    (hfv : fv ∈ projEdges K v ∧ γv ∈ fv ∧ IsTreeEdge K.H fv) :
    (fu ∉ projEdges K v → ¬ Prec G x y u v) ∧
    (fu = fv → γu = γv → ∀ (c : N) (σ : V → ℕ), fu = s(c, γu) → IsSigma G μ K c γu σ →
      σ u < σ v → ¬ Prec G x y u v) := by sorry

end BeyondGomoryHu.Units
