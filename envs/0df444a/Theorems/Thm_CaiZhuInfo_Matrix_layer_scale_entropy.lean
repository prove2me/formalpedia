-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_layer_scale_entropy
-- name    : CaiZhuInfo.Matrix.layer_scale_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:02.801872+00:00
-- url     : https://prove2.me/theorems/764d8df2-4308-48cb-b393-bf6635290870
-- title:
--   Lemma 4.2 — Entropy of the layer scale
-- statement:
--   Use the decreasing-support layer construction for a finitely supported group law $Q$, select layer number $J$ with probabilities $w_j=j(q_j-q_{j+1})$, and put $R=\lfloor\log_2J\rfloor$. Then
--   $$H(Q)\le H(R)+\mathbb ER+1.$$
--   The scale law and its mean are the actual sums induced by the computed layer weights. This retains the entropy of selecting a scale, as well as its expected size.
--
--   Differences from the source:
--   - encoding: the integer-valued scale R → its computed mass function on Fin(length+1), with unused values of mass zero; reason: adding zero-mass labels changes neither its law, entropy nor expectation
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 4.2, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_LayerData

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem layer_scale_entropy {G : Type} [Group G] (L : LayerData G) :
    L.supportEntropy ≤ FuchsVdGraaf.entropy L.scaleMass + L.scaleMean + 1 := by sorry

end CaiZhuInfo.Matrix
