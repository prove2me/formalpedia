-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_eq_4_reflected
-- name    : BenyOreshkov.AQEC.eq_4_reflected
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:22.827013+00:00
-- url     : https://prove2.me/theorems/e7b15cc7-2508-4e37-81c3-2a817510679d
-- title:
--   Proof of Theorem 1, p. 2 — reflected circuit, $F_\rho(\widehat{\mathcal N},\mathcal R'\widehat{\mathcal M})=\max_U|g_\rho(U,U')|$
-- statement:
--   Let $V_{\mathcal N}:A\to B\otimes E$ and $V_{\mathcal M}:A\to B'\otimes E'$ be isometries, with complementary channels $\widehat{\mathcal N}=\mathrm{Tr}_B(V_{\mathcal N}\cdot V_{\mathcal N}^\dagger)$ and $\widehat{\mathcal M}=\mathrm{Tr}_{B'}(V_{\mathcal M}\cdot V_{\mathcal M}^\dagger)$. Let $C : E'\to E\otimes K$ be an isometry, $K=\mathbb C^r$, defining the channel $\mathcal R'=\mathrm{Tr}_K(C\cdot C^\dagger)$ from $E'$ to $E$, and let $\rho$ be a state on $A$. Then
--   $$
--   F_\rho(\widehat{\mathcal N},\mathcal R'\widehat{\mathcal M}) = \max_{W : B\to B'\otimes K,\ \|W\|\le 1}\ \big|\mathrm{Tr}\big(G(V_{\mathcal N},V_{\mathcal M},W,C)\,\rho\big)\big|,
--   $$
--   with the same circuit operator $G$ as in Eq. (4), now maximized over the other operator; the maximum is attained. Taking the minimum over $\rho$ and the maximum over $C$ gives the paper's $\max_{\mathcal R'}F(\widehat{\mathcal N},\mathcal R'\widehat{\mathcal M})=\max_{U'}\min_\rho\max_U|g_\rho(U,U')|$, "where now $U'$ is the unitary defining $\mathcal R'$ while $U$ comes from Uhlmann's expression for the fidelity".
--
--   Differences from the source:
--   - generalization: max_R′ F(N̂, R′M̂) = max_U′ min_ρ max_U |g_ρ(U, U′)| → the inner identity F_ρ(N̂, R′M̂) = max_W |g_ρ(W, C)| for every state ρ and every isometry C; reason: taking min over ρ and max over C, with the Stinespring form of channels, gives the source's identity
--   - encoding: maximum over unitaries U (from Uhlmann) → maximum over contractions W : B → B′ ⊗ Fin r; reason: Uhlmann's maximum is the same over contractions, and the purifying systems differ in dimension
--   - encoding: the unitary U′ defining R′ → the isometry C = U′(· ⊗ |0⟩) : E′ → E ⊗ Fin r; reason: same channels
--   - encoding: g_ρ(U, U′), the circuit value on any purification |ψ_ρ⟩ → |Tr(gOp V_N V_M W C · ρ)|; reason: the circuit value is ⟨ψ_ρ|(1 ⊗ G)|ψ_ρ⟩ = Tr(Gρ) for every purification of ρ
--   - encoding: F_ρ with any purification |ψ⟩ and f(ρ, σ) = Tr √(√ρ σ √ρ) → entFid: the canonical purification (reference first) and QAlgorithms.rootFidelity with cfc Real.sqrt; reason: F_ρ does not depend on the purification; cfc Real.sqrt is the positive square root on the positive semidefinite arguments that occur
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, p. 2 (the reflected picture)

import Definitions.Def_BenyOreshkov_AQEC_stinespringMap
import Definitions.Def_BenyOreshkov_AQEC_entFid
import Definitions.Def_BenyOreshkov_AQEC_gOp
import Definitions.Def_PeresTerno_kraus_basics

open Matrix QAlgorithms WildeQIT
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **The reflected identity for `F_ρ(N̂, R′M̂)`.** Bény, Oreshkov, arXiv:0907.5391v4, proof of
Theorem 1, p. 2: reflecting the circuit gives
`max_R′ F(N̂, R′M̂) = max_U′ min_ρ max_U |g_ρ(U, U′)|`, "where now U′ is the unitary defining R′
while U comes from Uhlmann's expression for the fidelity". For isometries `V_N`, `V_M` (with
`N̂ = Tr_B(V_N · V_N†)`, `M̂ = Tr_{B′}(V_M · V_M†)`), an isometry `C : E′ → E ⊗ K` (the channel
`R′ = Tr_K(C · C†) : E′ → E`) and a density matrix `ρ`, the entanglement fidelity
`F_ρ(N̂, R′M̂)` is the largest value of `|Tr(gOp V_N V_M W C · ρ)|` over contractions
`W : B → B′ ⊗ K`, and it is attained.

**Formalization Note** Same operator `gOp` as in Eq. (4), maximized over the other argument.
Pointwise in `ρ` and `C` (Reading 9); `U` ranges over contractions (Reading 8). -/
theorem eq_4_reflected {A B E B' E' : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype E] [DecidableEq E] [Fintype B'] [DecidableEq B'] [Fintype E']
    [DecidableEq E'] {r : ℕ} (VN : Matrix (B × E) A ℂ) (VM : Matrix (B' × E') A ℂ)
    (hVN : VNᴴ * VN = 1) (hVM : VMᴴ * VM = 1) (C : Matrix (E × Fin r) E' ℂ) (hC : Cᴴ * C = 1)
    (ρ : Matrix A A ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    IsGreatest
      {t : ℝ | ∃ W : Matrix (B' × Fin r) B ℂ, Wᴴ * W ≤ 1 ∧ t = ‖(gOp VN VM W C * ρ).trace‖}
      (entFid ρ (stinespringComp VN) (stinespringMap C ∘ stinespringComp VM)) := by sorry

end BenyOreshkov.AQEC
