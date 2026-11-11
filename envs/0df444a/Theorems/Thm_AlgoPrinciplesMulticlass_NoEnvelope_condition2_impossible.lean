-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_condition2_impossible
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.condition2_impossible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:59.72602+00:00
-- url     : https://prove2.me/theorems/10d19c69-ad88-4f36-a8b5-4d571261d68c
-- title:
--   §3.1, Condition 2 paragraph — for a (possibly randomized) PAC learner of H, Condition 2 is impossible
-- statement:
--   Let $\mathcal H$ be the class of the §3.1 construction and let $A$ be a possibly randomized learner (internal randomness $\omega\sim\mu$) that PAC learns $\mathcal H$: for every $\varepsilon,\delta\in(0,1)$ there is $n_A(\varepsilon,\delta)$ with $\Pr_{S\sim D^m,\omega}[L_D(A_\omega(S),h^\star)>\varepsilon]\le\delta$ for all $m\ge n_A(\varepsilon,\delta)$, all $h^\star\in\mathcal H$ and all distributions $D$ on $X$. Let $\operatorname{im}(A)$ be the set of all its outputs. Then for every $d\ge1$, Condition 2 fails for $\operatorname{im}(A)$: there is **no** infinite sequence $b_1,b_2,\dots\in\{0,1\}^d$ with
--   $$b_i\notin\operatorname{im}(A){\restriction}E_{d,(b_1,\dots,b_{i-1})}\quad\text{for every } i\ge1 .$$
--
--   Together with Lemma 3.3 this leaves Condition 1 on every tree $T_d$, which gives $\mathrm{DS}(\operatorname{im}(A))=\infty$.
--
--   **Formalization Note.** A randomized learner is `RandLearner.{u} Pt Label` (definition `Randomized`), its PAC guarantee is `RandLearner.PACLearns` and its image `RandLearner.image`; a deterministic learner is the one-point case.
--
--   Differences from the source:
--   - encoding: a "(possibly randomized)" PAC learner A, a notion §2 does not define → `RandLearner`: a probability space (Ω, μ), learners A_ω, each prediction ω ↦ A_ω(S)(x) measurable, failure probability under D^m ⊗ μ, im(A) = ⋃_ω im(A_ω); reason: the measurability is exactly what makes the source's probability over the sample and A's internal randomness defined; deterministic learners are the one-point Ω
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 19, §3.1, Condition 2 paragraph (announced on p. 18)

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Randomized
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

namespace AlgoPrinciplesMulticlass.NoEnvelope

universe u

/-- §3.1, Condition 2 paragraph (p. 19): for every (possibly randomized) learner `A` that PAC
learns `H` and every `d ≥ 1`, Condition 2 fails for `im(A)`. -/
theorem condition2_impossible (R : RandLearner.{u} Pt Label) (hR : R.PACLearns H) (d : ℕ)
    (hd : 1 ≤ d) :
    ¬ Condition2 R.image d := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
