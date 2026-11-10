-- Prove2me | Theorems.Thm_CritContracts_lemma_3_3
-- name    : CritContracts.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:17.382128+00:00
-- url     : https://prove2.me/theorems/c10cf9b3-af37-4ee9-897b-4af08db85d03
-- title:
--   Lemma 3.3 — for supermodular $f$ every contract induces a supermodular game; $\mathrm{NE}(\alpha)$ is a nonempty complete lattice
-- statement:
--   Let $f$ be supermodular and let $\alpha\in[0,1]^n$ be a contract. Then the game induced among the agents is a **supermodular game**: for every agent $i$, every set $X$ of the other agents' actions and all $D,D'\subseteq T_i$,
--   $$u_i(\alpha,X\cup D)+u_i(\alpha,X\cup D')\le u_i(\alpha,X\cup(D\cup D'))+u_i(\alpha,X\cup(D\cap D')),$$
--   and $u_i$ has **increasing differences**: for $D\subseteq D'\subseteq T_i$ and $X\subseteq X'$ sets of the others' actions,
--   $$u_i(\alpha,X\cup D')-u_i(\alpha,X\cup D)\le u_i(\alpha,X'\cup D')-u_i(\alpha,X'\cup D).$$
--   Consequently:
--
--   1. $\mathrm{NE}(\alpha)$ is nonempty;
--   2. $\mathrm{NE}(\alpha)$ is a complete lattice under inclusion: every family $\mathcal S\subseteq\mathrm{NE}(\alpha)$ has a least upper bound and a greatest lower bound in $\mathrm{NE}(\alpha)$;
--   3. in particular $\mathrm{NE}(\alpha)$ has a least and a greatest element.
--
--   The greatest equilibrium $S^+(\alpha)$ is the equilibrium the paper's algorithms select; Lemma 3.10 and the proof of Theorem 3.5 use its monotonicity in $\alpha$.
--
--   **Formalization Note** The supremum of a family in the poset $(\mathrm{NE}(\alpha),\subseteq)$ is the least equilibrium containing every member; it need not be the union.
--
--   Differences from the source:
--
--   - generalization: Lemma 3.3 for a reward f: 2^T → [0,1] of §2 (monotone, normalized, costs c_j ≥ 0) → any real-valued supermodular f and any real costs; reason: the lemma's proof uses only supermodularity of f and α ≥ 0; instances of §2 are special cases
--   - encoding: NE(α) forms a complete lattice under set inclusion → every subset of NE(α) has a least upper bound and a greatest lower bound inside NE(α) w.r.t. ⊆; reason: definition of a complete lattice, stated for the subposet
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma 3.3, p.11 (PDF p.12); Definition 3.2, p.11

import Mathlib
import Definitions.Def_CritContracts_Model
import Definitions.Def_CritContracts_IsSupermodular
import Definitions.Def_CritContracts_IsGreatestBR

set_option autoImplicit false

namespace CritContracts

open Model

/-- **Lemma 3.3** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), §3.1, p.11, PDF p.12): let `f` be supermodular. For every contract `α`
the game induced among the agents is a supermodular game (Definition 3.2: each agent's utility is
supermodular in his own action set, and has increasing differences in his own and the others'
action sets). Consequently `NE(α)` is nonempty and forms a complete lattice under set inclusion
(every subset of `NE(α)` has a least upper bound and a greatest lower bound in `NE(α)`), and in
particular it has a least and a greatest equilibrium.

**Formalization Note** The complete-lattice clause is stated for the poset `(NE(α), ⊆)`: the
supremum of a family of equilibria is the least equilibrium containing all of them (it need not be
their union). The standing assumptions of §2 (`f` monotone, normalized, `[0,1]`-valued; costs
`≥ 0`) are not assumed: the lemma uses only supermodularity and `α ≥ 0`. -/
theorem lemma_3_3 {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (M : Model ι T) (hf : IsSupermodular M.f) (α : ι → ℝ) (hα : IsContract α) :
    (∀ (i : ι) (X D D' : Finset T), (∀ j ∈ X, M.owner j ≠ i) → (∀ j ∈ D, M.owner j = i) →
        (∀ j ∈ D', M.owner j = i) →
        M.agentUtil α i (X ∪ D) + M.agentUtil α i (X ∪ D') ≤
          M.agentUtil α i (X ∪ (D ∪ D')) + M.agentUtil α i (X ∪ (D ∩ D'))) ∧
    (∀ (i : ι) (X X' D D' : Finset T), (∀ j ∈ X', M.owner j ≠ i) → (∀ j ∈ D', M.owner j = i) →
        X ⊆ X' → D ⊆ D' →
        M.agentUtil α i (X ∪ D') - M.agentUtil α i (X ∪ D) ≤
          M.agentUtil α i (X' ∪ D') - M.agentUtil α i (X' ∪ D)) ∧
    (∃ S : Finset T, M.IsNE α S) ∧
    (∀ 𝒮 : Set (Finset T), 𝒮 ⊆ {S | M.IsNE α S} →
        (∃ G : Finset T, M.IsNE α G ∧ G ∈ upperBounds 𝒮 ∧
          ∀ H : Finset T, M.IsNE α H → H ∈ upperBounds 𝒮 → G ⊆ H) ∧
        (∃ G : Finset T, M.IsNE α G ∧ G ∈ lowerBounds 𝒮 ∧
          ∀ H : Finset T, M.IsNE α H → H ∈ lowerBounds 𝒮 → H ⊆ G)) ∧
    (∃ G : Finset T, IsLeast {S | M.IsNE α S} G) ∧
    (∃ G : Finset T, M.IsGreatestNE α G) := by sorry

end CritContracts
