-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_3_i
-- name    : EffResSparsify.Sampling.lemma_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:27.777202+00:00
-- url     : https://prove2.me/theorems/63ee1095-ae08-4b93-88af-c0d6bc8b40c4
-- title:
--   Lemma 3 (i) — $\Pi$ is a projection matrix
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph with positive edge weights, and let $\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}$, where $B$ is the signed incidence matrix, $W$ the diagonal weight matrix and $L^{+}$ the pseudoinverse of the Laplacian $L=B^{\mathsf T}WB$. Then $\Pi$ is an orthogonal projection matrix:
--   $$\Pi^2=\Pi\qquad\text{and}\qquad\Pi^{\mathsf T}=\Pi.$$
--
--   This is what lets spectral-norm approximation of $\Pi$ control quadratic forms, the reduction behind Lemma 4.
--
--   **Formalization Note** The paper's "projection matrix" is read as an orthogonal projection; symmetry is stated as a conjunct because the paper uses it in part (iv).
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 6, Lemma 3 (i)

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix

/-- Lemma 3 (i), p. 6: `Π = W^{1/2} B L⁺ Bᵀ W^{1/2}` is a projection matrix: it is idempotent
and symmetric. -/
theorem lemma_3_i {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) :
    G.projPi * G.projPi = G.projPi ∧ G.projPiᵀ = G.projPi := by sorry

end EffResSparsify.Sampling
