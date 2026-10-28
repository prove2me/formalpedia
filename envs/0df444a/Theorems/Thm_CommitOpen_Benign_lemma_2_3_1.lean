-- Prove2me | Theorems.Thm_CommitOpen_Benign_lemma_2_3_1
-- name    : CommitOpen.Benign.lemma_2_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:38.771965+00:00
-- url     : https://prove2.me/theorems/2d8e62a8-6b1c-4440-89ee-dbd26997ec41
-- title:
--   Lemma 2.3 (1), p. 3 — measuring a superposition of |J| product vectors loses at most log|J| bits of min-entropy
-- statement:
--   Let $\mathcal H_A$ and $\mathcal H_E$ be finite-dimensional, let $\{|i\rangle\}_{i\in I}$ be an orthonormal basis of $\mathcal H_A$, let $J\subseteq I$ be finite, and let
--   $$|\varphi_{AE}\rangle=\sum_{i\in J}\alpha_i|i\rangle|\varphi^i_E\rangle$$
--   with unit vectors $|\varphi^i_E\rangle$ and $\sum_{i\in J}|\alpha_i|^2=1$. Let $\tilde\rho_{AE}=\sum_{i\in J}|\alpha_i|^2|i\rangle\langle i|\otimes|\varphi^i_E\rangle\langle\varphi^i_E|$. Let $W$ and $\tilde W$ be the outcomes of measuring register $A$ of $|\varphi_{AE}\rangle$, respectively of $\tilde\rho_{AE}$, in an orthonormal basis $\{|w\rangle\}_{w\in\mathcal W}$. Then
--   $$H_\infty(W)\ge H_\infty(\tilde W)-\log|J|.$$
--
--   A pure state that is a superposition of few basis vectors behaves, for min-entropy, almost like the corresponding mixture. Corollary 4.4 applies this to the state Alice's register is left in after the test.
--
--   **Formalization Note.** $\log=\log_2$. The paper says "a basis"; the statement uses an orthonormal basis and unit $|\varphi^i_E\rangle$, both needed for $\tilde\rho_{AE}$ to be a state and for the outcome law of $\tilde W$, $P_{\tilde W}(w)=\sum_{i\in J}|\alpha_i|^2|\langle w|i\rangle|^2$. The outcome set $\mathcal W$ is assumed nonempty, which the other hypotheses already force.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 3, Lemma 2.3, item 1

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem lemma_2_3_1 {ι I W E : Type} [Fintype ι] [Fintype I] [Fintype W] [Nonempty W]
    [Fintype E] (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι))
    (w : OrthonormalBasis W ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (hφE : ∀ i ∈ J, ‖φE i‖ = 1)
    (hα : ∑ i ∈ J, ‖α i‖ ^ 2 = 1) :
    minEntropy (fun v => mixtureProb b J α (w v)) - Real.logb 2 (J.card : ℝ) ≤
      minEntropy (fun v => measProb (w v) (superposition b J α φE)) := by sorry

end CommitOpen.Benign
