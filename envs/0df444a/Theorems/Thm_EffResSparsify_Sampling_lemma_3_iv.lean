-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_3_iv
-- name    : EffResSparsify.Sampling.lemma_3_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:21.495065+00:00
-- url     : https://prove2.me/theorems/67582d48-b9c4-4754-84bf-3eecdfdf7969
-- title:
--   Lemma 3 (iv) — $\Pi(e,e)=\|\Pi(\cdot,e)\|^2$
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph with positive edge weights and $\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}$. For every edge $e$, the diagonal entry of $\Pi$ at $e$ equals the squared Euclidean norm of the $e$-th column of $\Pi$:
--   $$\Pi(e,e)=\|\Pi(\cdot,e)\|_2^2=\sum_{e'\in E}\Pi(e',e)^2.$$
--
--   Since $\Pi(e,e)=w_eR_e$, this bounds the length of the column sampled by Sparsify, which is the norm bound fed into the matrix concentration inequality (Lemma 5).
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 6, Lemma 3 (iv)

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix

/-- Lemma 3 (iv), p. 6: `Π(e,e) = ‖Π(·,e)‖²`, the squared Euclidean norm of the `e`-th column. -/
theorem lemma_3_iv {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (e : E) :
    G.projPi e e = ∑ e' : E, (G.projPi e' e) ^ 2 := by sorry

end EffResSparsify.Sampling
