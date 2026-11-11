-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_pac_learner_image_ds_infinite
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.pac_learner_image_ds_infinite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:29:06.361795+00:00
-- url     : https://prove2.me/theorems/fe08e07b-21b3-4370-9261-804103643ec4
-- title:
--   §3.1, the stronger statement — every (possibly randomized) PAC learner for H has an image of infinite DS dimension
-- statement:
--   Let $\mathcal H$ be the class of the §3.1 construction. Every possibly randomized learner $A$ that PAC learns $\mathcal H$ satisfies
--   $$\mathrm{DS}\big(\operatorname{im}(A)\big)=\infty,$$
--   where $\operatorname{im}(A)$ is the set of all hypotheses $A$ outputs, over all finite samples and all values of its internal randomness. The statement has two clauses: one for randomized learners and one for deterministic learners in the sense of §2.
--
--   This is the statement that "immediately proves Theorem 3.1": a proper learner for a class $\mathcal H_{\mathrm{prop}}\supseteq\mathcal H$ that PAC learns $\mathcal H_{\mathrm{prop}}$ also PAC learns $\mathcal H$ and has $\operatorname{im}(A)\subseteq\mathcal H_{\mathrm{prop}}$, so $\mathrm{DS}(\mathcal H_{\mathrm{prop}})=\infty$, which no learnable class allows.
--
--   **Formalization Note.** $\mathrm{DS}$ is `MulticlassDS.Compress.dsDim` (`ℕ∞`), and $=\infty$ is `= ⊤`. Randomized learners are `RandLearner.{u} Pt Label` with `RandLearner.PACLearns` and `RandLearner.image`; deterministic ones are `Learner Pt Label` with `PACLearns` and `Learner.image`.
--
--   Differences from the source:
--   - encoding: every "(possibly randomized)" PAC learner A, DS(im(A)) = ∞ → two clauses, `RandLearner` (probability space (Ω, μ), measurable predictions, failure probability under D^m ⊗ μ, im = ⋃_ω im(A_ω)) and deterministic `Learner`, each with `dsDim (image) = ⊤`; reason: §2 defines only deterministic learners; the randomized model is the minimal one in which the source's probability is defined, and both readings of "possibly randomized" are stated
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18, §3.1 (No properly learnable envelope exists), the stronger statement

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Randomized
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

namespace AlgoPrinciplesMulticlass.NoEnvelope

universe u

/-- §3.1, the stronger statement (p. 18): every (possibly randomized) PAC learner `A` for `H`
has `DS(im(A)) = ∞`; stated for randomized learners and, separately, for deterministic ones. -/
theorem pac_learner_image_ds_infinite :
    (∀ R : RandLearner.{u} Pt Label, R.PACLearns H →
      MulticlassDS.Compress.dsDim R.image = ⊤) ∧
    (∀ A : Learner Pt Label, PACLearns A H →
      MulticlassDS.Compress.dsDim A.image = ⊤) := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
