-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_eq_4
-- name    : BenyOreshkov.AQEC.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:30.721835+00:00
-- url     : https://prove2.me/theorems/9d67c210-53c3-468a-86db-cc3d7b1b26d8
-- title:
--   Eq. (4), p. 2 — $F_\rho(\mathcal R\mathcal N,\mathcal M)=\max_{U'}|g_\rho(U,U')|$
-- statement:
--   Let $V_{\mathcal N}:A\to B\otimes E$ and $V_{\mathcal M}:A\to B'\otimes E'$ be isometries, $\mathcal N=\mathrm{Tr}_E(V_{\mathcal N}\cdot V_{\mathcal N}^\dagger)$ and $\mathcal M=\mathrm{Tr}_{E'}(V_{\mathcal M}\cdot V_{\mathcal M}^\dagger)$. Let $W : B\to B'\otimes K$ be an isometry, $K=\mathbb C^r$, defining the recovery channel $\mathcal R=\mathrm{Tr}_K(W\cdot W^\dagger)$, and let $\rho$ be a state on $A$. Then
--   $$
--   F_\rho(\mathcal R\mathcal N,\mathcal M) = \max_{C : E'\to E\otimes K,\ \|C\|\le 1}\ \big|\mathrm{Tr}\big(G(V_{\mathcal N},V_{\mathcal M},W,C)\,\rho\big)\big|,
--   $$
--   where $G$ is the circuit operator, so that $\mathrm{Tr}(G\rho)=g_\rho(U,U')$; the maximum is attained. Taking the minimum over $\rho$ and the maximum over $W$ gives Eq. (4), $\max_{\mathcal R}F(\mathcal R\mathcal N,\mathcal M)=\max_U\min_\rho\max_{U'}|g_\rho(U,U')|$.
--
--   Differences from the source:
--   - generalization: Eq. (4), an identity of max_U min_ρ max_U′ → the inner identity F_ρ(RN, M) = max_C |g_ρ(W, C)| for every state ρ and every isometry W; reason: taking min over ρ and max over W, with the Stinespring form of channels, gives Eq. (4)
--   - encoding: maximum over unitaries U′ → maximum over contractions C : E′ → E ⊗ Fin r; reason: Uhlmann's maximum is the same over contractions (the source's own unit-ball remark on p. 2), and the purifying systems differ in dimension
--   - encoding: U on B ⊗ |0⟩ → the isometry W = U(· ⊗ |0⟩) : B → B′ ⊗ Fin r; reason: same channels
--   - encoding: g_ρ(U, U′), the circuit value on any purification |ψ_ρ⟩ → |Tr(gOp V_N V_M W C · ρ)|; reason: the circuit value is ⟨ψ_ρ|(1 ⊗ G)|ψ_ρ⟩ = Tr(Gρ) for every purification of ρ
--   - encoding: F_ρ with any purification |ψ⟩ and f(ρ, σ) = Tr √(√ρ σ √ρ) → entFid: the canonical purification (reference first) and QAlgorithms.rootFidelity with cfc Real.sqrt; reason: F_ρ does not depend on the purification; cfc Real.sqrt is the positive square root on the positive semidefinite arguments that occur
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, Eq. (4) and the circuit for g_ρ, p. 2

import Definitions.Def_BenyOreshkov_AQEC_stinespringMap
import Definitions.Def_BenyOreshkov_AQEC_entFid
import Definitions.Def_BenyOreshkov_AQEC_gOp
import Definitions.Def_PeresTerno_kraus_basics

open Matrix QAlgorithms WildeQIT
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **Eq. (4): `F_ρ(RN, M)` is a maximized overlap `g_ρ`.** Bény, Oreshkov, arXiv:0907.5391v4,
proof of Theorem 1, Eq. (4), p. 2: `max_R F(RN, M) = max_U min_ρ max_U′ |g_ρ(U, U′)|`. For
isometries `V_N : A → B ⊗ E`, `V_M : A → B′ ⊗ E′` (so `N = Tr_E(V_N · V_N†)`,
`M = Tr_{E′}(V_M · V_M†)`), an isometry `W : B → B′ ⊗ K` (the recovery `R = Tr_K(W · W†)`) and a
density matrix `ρ`, the entanglement fidelity `F_ρ(RN, M)` is the largest value of
`|g_ρ(W, C)| = |Tr(gOp V_N V_M W C · ρ)|` over contractions `C : E′ → E ⊗ K`, and it is attained.

**Formalization Note** Stated pointwise in `ρ` and `W` (Reading 9): taking the minimum over `ρ`
and the maximum over `W`, with `isChannel_iff_stinespring`, gives Eq. (4). `U′` ranges over
contractions (Reading 8, the unit-ball form p. 2 ends with). The environment of `W` and `C` is
`Fin r`. -/
theorem eq_4 {A B E B' E' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Fintype B'] [DecidableEq B'] [Fintype E'] [DecidableEq E']
    {r : ℕ} (VN : Matrix (B × E) A ℂ) (VM : Matrix (B' × E') A ℂ) (hVN : VNᴴ * VN = 1)
    (hVM : VMᴴ * VM = 1) (W : Matrix (B' × Fin r) B ℂ) (hW : Wᴴ * W = 1) (ρ : Matrix A A ℂ)
    (hρ : PeresTerno.IsDensityMatrix ρ) :
    IsGreatest
      {t : ℝ | ∃ C : Matrix (E × Fin r) E' ℂ, Cᴴ * C ≤ 1 ∧ t = ‖(gOp VN VM W C * ρ).trace‖}
      (entFid ρ (stinespringMap W ∘ stinespringMap VN) (stinespringMap VM)) := by sorry

end BenyOreshkov.AQEC
