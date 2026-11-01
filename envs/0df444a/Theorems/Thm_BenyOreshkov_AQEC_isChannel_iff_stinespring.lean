-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_isChannel_iff_stinespring
-- name    : BenyOreshkov.AQEC.isChannel_iff_stinespring
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:02.291474+00:00
-- url     : https://prove2.me/theorems/51a1f0df-3029-446a-b051-2289add9ee2a
-- title:
--   Proof of Theorem 1, p. 2 — a map is a channel iff it is $\rho\mapsto\mathrm{Tr}_K(W\rho W^\dagger)$ for an isometry $W$
-- statement:
--   Let $X$, $Y$ be finite-dimensional Hilbert spaces and $\mathcal R$ a map from operators on $X$ to operators on $Y$. Then $\mathcal R$ is a quantum channel (it has a finite family of Kraus operators $E_j : X\to Y$ with $\sum_j E_j^\dagger E_j = 1$ and $\mathcal R(\rho)=\sum_j E_j\rho E_j^\dagger$) if and only if there are a finite-dimensional environment $K=\mathbb C^r$ and an isometry $W : X\to Y\otimes K$ with
--   $$
--   \mathcal R(\rho) = \mathrm{Tr}_K\big(W\rho W^\dagger\big)\qquad\text{for every operator }\rho.
--   $$
--   This is the paper's remark that "for a fixed state $|0\rangle$, any channel $\mathcal R$ can be written as $\mathcal R(\rho)=\mathrm{Tr}_{\widetilde E}(U(\rho\otimes|0\rangle\langle0|)U^\dagger)$", together with the converse, which the proof uses when it replaces the maximum over channels $\mathcal R$ by a maximum over unitaries $U$.
--
--   **Formalization Note** The isometry $W$ stands for $U(\cdot\otimes|0\rangle)$; every isometry has this form.
--
--   Differences from the source:
--   - generalization: "any channel R can be written as Tr_Ẽ(U(ρ ⊗ |0⟩⟨0|)U†)" (one direction) → an iff: channel ⟺ Stinespring form with an isometry; reason: the proof also uses the converse when it maximizes over U instead of R; the forward direction is the source's claim
--   - encoding: a unitary U on ρ ⊗ |0⟩⟨0| → an isometry W = U(· ⊗ |0⟩) : X → Y ⊗ Fin r; reason: every such W is an isometry and every isometry extends to a unitary; same maps
--   - encoding: quantum channel → a finite normalized Kraus family (QAlgorithms.IsChannel); reason: in finite dimension these are exactly the CPTP maps
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, p. 2

import Definitions.Def_BenyOreshkov_AQEC_stinespringMap

open Matrix QAlgorithms WildeQIT

namespace BenyOreshkov.AQEC

/-- **Stinespring form of a channel.** Bény, Oreshkov, arXiv:0907.5391v4, §Main result, proof of
Theorem 1, p. 2: "for a fixed state |0⟩, any channel R can be written as
R(ρ) = Tr_Ẽ(U(ρ ⊗ |0⟩⟨0|)U†) for some unitary U and appropriate environment Ẽ". A superoperator
`R : X → Y` is a channel (a finite normalized Kraus family) if and only if
`R(ρ) = Tr_K(W ρ W†)` for an isometry `W : X → Y ⊗ K` with `K = Fin r` for some `r`.

**Formalization Note** The paper's `U(· ⊗ |0⟩)` is the isometry `W`, and every isometry arises
this way (Reading 8). The converse direction (every such map is a channel) is what the proof uses
when it maximizes over `U` instead of `R`. -/
theorem isChannel_iff_stinespring {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (R : Superop X Y) :
    IsChannel R ↔ ∃ (r : ℕ) (W : Matrix (Y × Fin r) X ℂ), Wᴴ * W = 1 ∧ ∀ ρ, R ρ = stinespringMap W ρ := by sorry

end BenyOreshkov.AQEC
