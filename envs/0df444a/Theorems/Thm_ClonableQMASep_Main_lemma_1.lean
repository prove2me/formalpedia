-- Prove2me | Theorems.Thm_ClonableQMASep_Main_lemma_1
-- name    : ClonableQMASep.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:12.715065+00:00
-- url     : https://prove2.me/theorems/f7622216-6315-45a1-97d1-e70fc4b9e26c
-- title:
--   Lemma 1 — Hybrid Lemma [BBBV97]
-- statement:
--   Let $f,g:X\to\{0,1\}^r$ agree outside $S\subseteq X$. Consider a $T$-query algorithm started from a unit vector, with final states $\rho^f,\rho^g$, and let $\rho^f_t$ be its state immediately before the $t$-th query in the $f$-execution. Put
--   $$p_t(S)=\operatorname{Tr}\big((\Pi_S\otimes I)\rho^f_t\big),\qquad\Pi_S=\sum_{x\in S}|x\rangle\langle x| .$$
--   Then
--   $$D(\rho^f,\rho^g)\le2\sum_{t=1}^T\sqrt{p_t(S)}\le2\Big(T\sum_{t=1}^Tp_t(S)\Big)^{1/2},$$
--   and the same bound applies to the difference between the probabilities of any acceptance event (orthogonal projector) in the two executions.
--
--   This is the query-magnitude hybrid argument; it is used in Lemma 7 to show that a verifier distinguishing $M[H]$ from $M[H,E]$ must place query weight on the inputs where they differ.
--
--   Differences from the source:
--
--   - encoding: a T-query algorithm with oracle-independent quantum operations between queries → unitaries U_0, …, U_T on X × R × W with an arbitrary finite workspace W, started from a unit vector; reason: measurements are deferred by purification (§2.2); a dilated algorithm has the same query weights and its reduced final states are no farther apart
--   - encoding: the two acceptance probabilities → ‖P ρ‖ probabilities for every orthogonal projector P; reason: an algorithm's acceptance probability is that of its final projective measurement
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), Lemma 1, p. 11

import Definitions.Def_ClonableQMASep_Main_QueryModel

set_option autoImplicit false

namespace ClonableQMASep.Main

/-- Lemma 1 (Hybrid Lemma [BBBV97], p. 11). Let `f, g : X → {0,1}^r` agree outside `S`, and let
`A` be a `T`-query algorithm started from a unit vector `ψ₀`. With `p_t(S)` the query weight on `S`
of the state immediately before the `t`-th query in the `f`-execution,
`D(ρ^f, ρ^g) ≤ 2 ∑_t √p_t(S) ≤ 2 (T ∑_t p_t(S))^{1/2}`, and the same bound holds for the
difference of the probabilities of every projective acceptance event. -/
theorem lemma_1 {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] {r : ℕ}
    (f g : X → (Fin r → ZMod 2)) (S : Set X) (hfg : ∀ x, x ∉ S → f x = g x)
    (A : QueryAlgo X (Fin r → ZMod 2) W) (ψ₀ : X × (Fin r → ZMod 2) × W → ℂ)
    (hψ₀ : ∑ q, Complex.normSq (ψ₀ q) = 1) :
    traceDist (pureDM (stepState A f ψ₀ A.T)) (pureDM (stepState A g ψ₀ A.T)) ≤
        2 * ∑ t : Fin A.T, Real.sqrt (queryWeight S (stepState A f ψ₀ t.val)) ∧
      2 * ∑ t : Fin A.T, Real.sqrt (queryWeight S (stepState A f ψ₀ t.val)) ≤
        2 * Real.sqrt ((A.T : ℝ) * ∑ t : Fin A.T, queryWeight S (stepState A f ψ₀ t.val)) ∧
      ∀ P : Matrix (X × (Fin r → ZMod 2) × W) (X × (Fin r → ZMod 2) × W) ℂ, IsProjector P →
        |projProb P (stepState A f ψ₀ A.T) - projProb P (stepState A g ψ₀ A.T)| ≤
          2 * ∑ t : Fin A.T, Real.sqrt (queryWeight S (stepState A f ψ₀ t.val)) := by sorry

end ClonableQMASep.Main
