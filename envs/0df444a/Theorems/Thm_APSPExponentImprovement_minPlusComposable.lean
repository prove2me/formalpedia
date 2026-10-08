-- Prove2me | Theorems.Thm_APSPExponentImprovement_minPlusComposable
-- name    : APSPExponentImprovement.minPlusComposable
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T16:49:21.104442+00:00
-- url     : https://prove2.me/theorems/a0a26e9a-ddcc-4141-a040-e84c9ead04ff
-- title:
--   Composable min-plus multiplication at exponent 2.99825 up to logarithmic factors
-- statement:
--   For every fixed polynomial bound on integer input weights, there is a deterministic min-plus matrix multiplication procedure in the source word-RAM programming model whose running time is
--
--   $$O\!\left(n^{2.99825}(\log n+1)^c\right)$$
--
--   for some constant $c$. The procedure satisfies the model's correctness, memory and word-size contracts, so it can be called by the repeated-squaring APSP algorithm. This is the composable intermediate result used to obtain the mission's $O(n^{2.9983})$ APSP bound.
--
--   References:
--
--   1. [Alman and Vassilevska Williams, conclusion and footnote 10](https://arxiv.org/html/2610.06783v1#S6).
--   2. [Vassilevska Williams and Williams, subcubic equivalences](https://theory.stanford.edu/~virgi/tria-mmult-jv.pdf).
--   3. [Source word-RAM formalization](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp).
-- source:
--   https://arxiv.org/html/2610.06783v1#S6

import Definitions.Def_APSPSource_RemainingDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem APSPExponentImprovement.minPlusComposable :
    ThreeSumApsp.Claim.MinPlusInPolylog Light.lightModel 2.99825 := by sorry
