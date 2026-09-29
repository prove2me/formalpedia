-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_lemma10
-- name    : ExactSDPDuality.ELSD.lemma10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:15:32.120153+00:00
-- url     : https://prove2.me/theorems/9a39dd01-59ee-4fe7-b152-d91c57e4b0d9
-- title:
--   Lemma 10 — monotonicity and subspace structure of 𝒰ₖ, 𝒲ₖ, Q*(𝒲ₖ)
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices, with $G$, $Q^*$, $\mathcal U_k$, $\mathcal W_k$ as in the Extended Lagrange–Slater Dual. Then:
--
--   1. the sequences $\mathcal U_k$ and $\mathcal W_k$ ($k\ge 1$) are increasing: $\mathcal U_k\subseteq\mathcal U_{k+1}$ and $\mathcal W_k\subseteq\mathcal W_{k+1}$;
--   2. for every $k\le m$, $\mathcal W_k$ is a linear subspace of $\mathcal M_n$ and $Q^*(\mathcal W_k)$ is a linear subspace of $\mathbb R^m$;
--   3. $Q^*(\mathcal W_1)\subseteq\cdots\subseteq Q^*(\mathcal W_m)$;
--   4. if $0\in G$, then
--   $$G\subseteq \big(Q^*(\mathcal W_k)\big)^\perp\qquad\text{for every } k = 1,\dots,m .$$
--
--   The lemma gives the dual's constraint sets the structure of a nested chain of subspaces, which is what bounds the number of steps in the description of the polar (Theorem 12).
--
--   **Formalization Note** "Linear subspace" is stated as: the set is the carrier of a submodule. The orthogonal complement is taken with respect to the dot product. Part 3 is stated as $Q^*(\mathcal W_j)\subseteq Q^*(\mathcal W_k)$ for $1\le j\le k\le m$.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 141, Lemma 10

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Lemma 10 (Ramana 1997, p. 141):
(i) `𝒰ₖ` and `𝒲ₖ` are increasing set sequences;
(ii) for `k ≤ m`, `𝒲ₖ ⊆ ℳₙ` and `Q*(𝒲ₖ) ⊆ ℝᵐ` are linear subspaces;
(iii) `Q*(𝒲₁) ⊆ ⋯ ⊆ Q*(𝒲ₘ)`;
(iv) if `0 ∈ G`, then `G ⊆ (Q*(𝒲ₖ))^⊥` for every `k = 1, …, m`. -/
theorem lemma10 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    (∀ k, 1 ≤ k → Uset Q0 Q k ⊆ Uset Q0 Q (k + 1) ∧ Wset Q0 Q k ⊆ Wset Q0 Q (k + 1)) ∧
      (∀ k, k ≤ m →
        (∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
            (S : Set (Matrix (Fin n) (Fin n) ℝ)) = Wset Q0 Q k) ∧
          ∃ S : Submodule ℝ (Fin m → ℝ), (S : Set (Fin m → ℝ)) = Qstar Q '' Wset Q0 Q k) ∧
      (∀ j k, 1 ≤ j → j ≤ k → k ≤ m → Qstar Q '' Wset Q0 Q j ⊆ Qstar Q '' Wset Q0 Q k) ∧
      ((0 : Fin m → ℝ) ∈ feasibleSet Q0 Q →
        ∀ k, 1 ≤ k → k ≤ m → feasibleSet Q0 Q ⊆ perp (Qstar Q '' Wset Q0 Q k)) := by sorry

end ExactSDPDuality.ELSD
