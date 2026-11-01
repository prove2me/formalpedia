-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_unit_ball_relaxation
-- name    : BenyOreshkov.AQEC.unit_ball_relaxation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:22.413636+00:00
-- url     : https://prove2.me/theorems/09f18a8b-705b-4e60-858c-fdf3bacf4688
-- title:
--   Proof of Theorem 1, p. 2 — the max over $U$ in Eq. (4) may be taken over the unit ball $\|A\|\le 1$
-- statement:
--   Let $A$ be a nonempty finite-dimensional input space, $V_{\mathcal N}:A\to B\otimes E$ and $V_{\mathcal M}:A\to B'\otimes E'$ isometries with $\mathcal N=\mathrm{Tr}_E(V_{\mathcal N}\cdot V_{\mathcal N}^\dagger)$ and $\mathcal M=\mathrm{Tr}_{E'}(V_{\mathcal M}\cdot V_{\mathcal M}^\dagger)$, and let $W : B\to B'\otimes K$, $K=\mathbb C^r$, be an operator of norm $\|W\|\le 1$. Then there is a channel $\mathcal R$ from $B$ to $B'$ such that for every state $\rho$ on $A$ and every operator $C : E'\to E\otimes K$ with $\|C\|\le1$,
--   $$
--   \big|\mathrm{Tr}\big(G(V_{\mathcal N},V_{\mathcal M},W,C)\,\rho\big)\big| \le F_\rho(\mathcal R\mathcal N,\mathcal M).
--   $$
--   Since every isometry is a contraction, this shows (with Eq. (4)) that "the max over $U$ in Eq. (4) can as well be taken over the convex set of operators $A$ with operator norm $\|A\|\le1$".
--
--   Differences from the source:
--   - generalization: the max over U in Eq. (4) can be taken over the unit ball → for each contraction W one channel R with |g_ρ(W, C)| ≤ F_ρ(RN, M) for every state ρ and every contraction C; reason: taking max over C, min over ρ and max over W gives that the max–min–max over contractions is at most max_R F(RN, M); the reverse inequality holds because isometries are contractions, so this gives the source's claim
--   - encoding: input space A of positive dimension → [Nonempty A]; reason: for A of dimension zero there may be no channel B → B′ (B′ of dimension zero), while for nonempty A the isometry V_M forces B′ nonempty; the statement is undefined only in that case
--   - encoding: g_ρ(U, U′), the circuit value on any purification |ψ_ρ⟩ → |Tr(gOp V_N V_M W C · ρ)|; reason: the circuit value is ⟨ψ_ρ|(1 ⊗ G)|ψ_ρ⟩ = Tr(Gρ) for every purification of ρ
--   - encoding: F_ρ with any purification |ψ⟩ and f(ρ, σ) = Tr √(√ρ σ √ρ) → entFid: the canonical purification (reference first) and QAlgorithms.rootFidelity with cfc Real.sqrt; reason: F_ρ does not depend on the purification; cfc Real.sqrt is the positive square root on the positive semidefinite arguments that occur
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, p. 2 ("using the strong concavity of the fidelity, it can be shown ...")

import Definitions.Def_BenyOreshkov_AQEC_stinespringMap
import Definitions.Def_BenyOreshkov_AQEC_entFid
import Definitions.Def_BenyOreshkov_AQEC_gOp
import Definitions.Def_PeresTerno_kraus_basics

open Matrix QAlgorithms WildeQIT
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **The maximum over `U` may be taken over the unit ball.** Bény, Oreshkov,
arXiv:0907.5391v4, proof of Theorem 1, p. 2: "using the strong concavity of the fidelity, it can
be shown that the max over U in Eq. (4) can as well be taken over the convex set of operators A
with operator norm ‖A‖ ≤ 1". For isometries `V_N`, `V_M` and a contraction `W : B → B′ ⊗ K`
there is a channel `R : B → B′` such that, for every density matrix `ρ` and every contraction
`C : E′ → E ⊗ K`, `|Tr(gOp V_N V_M W C · ρ)| ≤ F_ρ(RN, M)`.

**Formalization Note** One channel `R` serves every `ρ` and `C` (Reading 9); with Eq. (4) this
gives that the max–min–max over contractions `W` equals the one over isometries. `[Nonempty A]`
is needed only so that a channel `B → B′` exists (for `A` nonempty the isometry `V_M` forces
`B′` nonempty). -/
theorem unit_ball_relaxation {A B E B' E' : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E] [Fintype B'] [DecidableEq B']
    [Fintype E'] [DecidableEq E'] {r : ℕ} (VN : Matrix (B × E) A ℂ) (VM : Matrix (B' × E') A ℂ)
    (hVN : VNᴴ * VN = 1) (hVM : VMᴴ * VM = 1) (W : Matrix (B' × Fin r) B ℂ) (hW : Wᴴ * W ≤ 1) :
    ∃ R : Superop B B', IsChannel R ∧
      ∀ ρ : Matrix A A ℂ, PeresTerno.IsDensityMatrix ρ →
        ∀ C : Matrix (E × Fin r) E' ℂ, Cᴴ * C ≤ 1 →
          ‖(gOp VN VM W C * ρ).trace‖ ≤ entFid ρ (R ∘ stinespringMap VN) (stinespringMap VM) := by sorry

end BenyOreshkov.AQEC
