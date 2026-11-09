-- Prove2me | Theorems.Thm_CutRankSched_lemma_3_3
-- name    : CutRankSched.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:35:11.876221+00:00
-- url     : https://prove2.me/theorems/b1de0e6b-027f-4b5c-aa6a-51e9272d1b1c
-- title:
--   Lemma 3.3 — residual-conflict reduction
-- statement:
--   Let $\lambda : [n] \to [L]$ be any layer assignment of an instance. Then $\lambda$ satisfies the constraints (2) if and only if it satisfies the anticommutation precedences together with $\lambda_i \ne \lambda_j$ for **all** overlapping pairs:
--   $$
--   (2) \iff \Bigl( A_{ij} = 1,\ i < j \Rightarrow \lambda_i < \lambda_j \Bigr) \wedge \Bigl( \{i, j\} \in E_X \Rightarrow \lambda_i \ne \lambda_j \Bigr).
--   $$
--   Hence, for a schedule, any two distinct events in the same layer have vertex-disjoint exposure regions: $\lambda_i = \lambda_j,\ i \ne j \Rightarrow V(T_i) \cap V(T_j) = \emptyset$.
--
--   The lemma shows that the residual graph $X^\circ$ loses nothing: each layer of a schedule is an independent set of the full overlap graph, i.e. a valid conservative round.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the proof uses only the partition E_X = E(X°) ⊔ (E_X ∩ E_anti) and the symmetry of A; valid instances are a special case
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Lemma 3.3, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Overlap
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_IsSchedule

set_option autoImplicit false

namespace CutRankSched

/-- **Lemma 3.3 (Residual-conflict reduction)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Lemma 3.3, p.5). The constraints (2) are
equivalent to the anticommutation precedence constraints together with `λ_i ≠ λ_j` for all
`{i, j} ∈ E_X`. Hence every layer of a schedule contains pairwise vertex-disjoint exposure regions.

**Formalization Note** 0-based events and layers; `E_X` on distinct pairs (`Overlap`). The lemma
holds for every instance, valid or not. -/
theorem lemma_3_3 (I : Instance) (L : ℕ) (lam : Fin I.n → Fin L) :
    (IsSchedule I L lam ↔
      ((∀ i j : Fin I.n, i < j → A I i j = 1 → lam i < lam j) ∧
        ∀ i j : Fin I.n, Overlap I i j → lam i ≠ lam j)) ∧
    (IsSchedule I L lam → ∀ i j : Fin I.n, i ≠ j → lam i = lam j →
      Disjoint (I.T i).verts (I.T j).verts) := by sorry

end CutRankSched
