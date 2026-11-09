-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_deterministic_local_decoding
-- name    : CaiZhuInfo.Matrix.deterministic_local_decoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:29.147209+00:00
-- url     : https://prove2.me/theorems/4a7e6936-fd5c-41ad-91b4-d455fc995981
-- title:
--   Lemma E.1 — Deterministic local decoding
-- statement:
--   For any Bob-only finite-output protocol on arbitrary discrete input alphabets, any fixed input distribution $\mu$ and any target function $f$, there is a measurable deterministic decoder $z(Y,\Pi)$ whose replacement protocol satisfies
--   $$P_\mu(z(Y,\Pi)\ne f(X,Y))\le P_\mu(\widehat f\ne f(X,Y)).$$
--   The transcript distribution and information cost are exactly unchanged. The conclusion concerns average error; it makes no pointwise derandomization claim. This permits prediction inequalities to be applied to protocol posteriors.
--
--   Differences from the source:
--   - encoding: finite randomized protocols with public and private randomness → finite binary trees with independent measurable tape probability spaces and derived execution laws; reason: finite messages admit binary coding and arbitrary real mixture probabilities are retained; no common round bound is imposed
--   - encoding: information cost I(X;Π | Y) + I(Y;Π | X), with Π containing the public tape and every message → I(H;X | Y,R) + I(H;Y | X,R), where H is the finite complete-history label and R is the public tape; reason: independence of the public tape from the inputs, the chain rule and symmetry of conditional mutual information give the same cost; the finite first slot also covers infinite discrete input alphabets
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma E.1, printed p.33 / PDF p.34; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem deterministic_local_decoding {X Y Z : Type}
    [Fintype Z]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (P : Protocol X Y Z) (μ : PMF (X × Y)) (f : X → Y → Z) :
    ∃ (z : Y → P.Transcript → Z)
      (hz : ∀ y, @Measurable _ Z inferInstance ⊤ (z y)),
      (P.replaceDecoder z hz).averageError μ f ≤ P.averageError μ f ∧
      (P.replaceDecoder z hz).transcriptLaw μ = P.transcriptLaw μ ∧
      (P.replaceDecoder z hz).informationCost μ = P.informationCost μ := by sorry

end CaiZhuInfo.Matrix
