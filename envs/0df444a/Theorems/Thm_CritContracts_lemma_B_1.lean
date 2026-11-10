-- Prove2me | Theorems.Thm_CritContracts_lemma_B_1
-- name    : CritContracts.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:44:57.377101+00:00
-- url     : https://prove2.me/theorems/77b83a09-a87a-4f20-bd18-f3472c1171be
-- title:
--   Lemma B.1 — $S(\lambda)$ is a pure Nash equilibrium and maximizes the reward over $\mathrm{NE}(\lambda)$
-- statement:
--   Consider an instance of the form (2): agent 1 owns $U$, agent 2 owns $V$, and $f(A,B)=\sum_{u\in A,v\in B}f_{uv}$ with $f_{uv}\ge0$. For every $\lambda\in\mathbb R^2_+$, the union $S(\lambda)$ of all $\lambda$-stable profiles is a pure Nash equilibrium at payments $\lambda$, and
--   $$\max_{S\in\mathrm{NE}(\lambda)}f(S)=f(S(\lambda)).$$
--
--   Lemmas B.2–B.8 analyse the reduction's graph through $S(\lambda)$; this lemma turns those statements into statements about the best equilibrium.
--
--   **Formalization Note** The payments are not required to be a contract. The maximum is stated as $S(\lambda)\in\mathrm{NE}(\lambda)$ together with $f(S)\le f(S(\lambda))$ for every $S\in\mathrm{NE}(\lambda)$.
--
--   Differences from the source:
--
--   - generalization: vertex costs c ≥ 0 (the model of §2) → arbitrary real vertex costs; reason: the proof (closure of stable profiles under union, additivity of utilities) never uses the sign of costs; the instances of §2 are special cases
--   - encoding: max_{S ∈ NE(λ)} f(S) = f(S(λ)) → S(λ) ∈ NE(λ) and f(S) ≤ f(S(λ)) for all S ∈ NE(λ); reason: the same statement
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.1, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_CritContracts_Model
import Definitions.Def_CritContracts_BipInst

set_option autoImplicit false

namespace CritContracts

/-- **Lemma B.1** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1, p.33, PDF p.34): for every instance of the form (2) (a
quadratic reward `f(A, B) = Σ_{u ∈ A, v ∈ B} f_uv` with `f_uv ≥ 0` on a bipartite graph whose two
sides are the two agents' action sets) and every `λ ∈ ℝ²₊`, the profile `S(λ)` (the union of all
`λ`-stable profiles) is a pure Nash equilibrium at payments `λ`, and
`max_{S ∈ NE(λ)} f(S) = f(S(λ))`.

**Formalization Note** The payments `λ` are not required to be a contract (`IsNE` accepts any
real payment vector). The maximum is stated as: `S(λ) ∈ NE(λ)` and `f(S) ≤ f(S(λ))` for every
`S ∈ NE(λ)`. Vertex costs are arbitrary reals (the model's `c ≥ 0` is not used). -/
theorem lemma_B_1 {X : Type} [Fintype X] [DecidableEq X] (I : BipInst X)
    (hw : ∀ u v : X, I.side u = 0 → I.side v = 1 → 0 ≤ I.w u v)
    (lam : Fin 2 → ℝ) (hlam : ∀ s, 0 ≤ lam s) :
    I.toModel.IsNE lam (I.stableUnion lam) ∧
      ∀ S : Finset X, I.toModel.IsNE lam S → I.reward S ≤ I.reward (I.stableUnion lam) := by sorry

end CritContracts
