-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_3_ii
-- name    : EffResSparsify.Sampling.lemma_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:27.124812+00:00
-- url     : https://prove2.me/theorems/64fa9fbb-ca6b-447c-aac8-636c1c03eba4
-- title:
--   Lemma 3 (ii) — $\operatorname{im}(\Pi)=\operatorname{im}(W^{1/2}B)$
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph with positive edge weights, with incidence matrix $B$, diagonal weight matrix $W$ and $\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}$. Then $\Pi$ and $W^{1/2}B$ have the same column space in $\mathbb R^E$:
--   $$\operatorname{im}(\Pi)=\operatorname{im}(W^{1/2}B).$$
--
--   In particular $\Pi$ acts as the identity on $\operatorname{im}(W^{1/2}B)$, the weighted cut space, which is the property Lemma 4 uses.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 6, Lemma 3 (ii)

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix

/-- Lemma 3 (ii), p. 6: `im(Π) = im(W^{1/2} B)`. -/
theorem lemma_3_ii {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) :
    LinearMap.range (Matrix.toLin' G.projPi) =
      LinearMap.range (Matrix.toLin' (G.sqrtWeightMatrix * G.incidence)) := by sorry

end EffResSparsify.Sampling
