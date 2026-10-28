-- Prove2me | Theorems.Thm_CommitOpen_Benign_lemma_2_3_2
-- name    : CommitOpen.Benign.lemma_2_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:44.299706+00:00
-- url     : https://prove2.me/theorems/b63a08d9-5d72-404d-81c4-57e28d84b18e
-- title:
--   Lemma 2.3 (2), p. 4 — the reduced state of a superposition of |J| product vectors has max-entropy at most log|J|
-- statement:
--   Let $\{|i\rangle\}_{i\in I}$ be an orthonormal basis of the finite-dimensional space $\mathcal H_A$, let $J\subseteq I$ be finite, and let $|\varphi_{AE}\rangle=\sum_{i\in J}\alpha_i|i\rangle|\varphi^i_E\rangle$ for arbitrary coefficients $\alpha_i$ and vectors $|\varphi^i_E\rangle$ of a finite-dimensional $\mathcal H_E$. Then the reduced density matrix $\rho_E=\operatorname{tr}_A(|\varphi_{AE}\rangle\langle\varphi_{AE}|)$ satisfies
--   $$H_0(\rho_E)\le\log|J|.$$
--
--   Bob's register, entangled with a superposition of few of Alice's basis states, can hold only few qubits' worth of state. Corollary 4.4 uses this for the bound on Bob's memory.
--
--   **Formalization Note.** $\log=\log_2$ and $H_0(\rho)=\log_2\operatorname{rank}\rho$. No normalization of $|\varphi_{AE}\rangle$ or of the $|\varphi^i_E\rangle$ is assumed: the rank bound does not need it, and a normalized state is a special case.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 4, Lemma 2.3, item 2

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem lemma_2_3_2 {ι I E : Type} [Fintype ι] [Fintype I] [Fintype E]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) :
    maxEntropy (reducedE (superposition b J α φE)) ≤ Real.logb 2 (J.card : ℝ) := by sorry

end CommitOpen.Benign
