-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_learnable_ds_finite
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.learnable_ds_finite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:22.50146+00:00
-- url     : https://prove2.me/theorems/a9d58eb9-8406-4f9f-9148-83a625b6f76d
-- title:
--   Cited fact (p. 18, from p. 4 [BCD+22, Pab26]) — a PAC learnable multiclass class has finite DS dimension
-- statement:
--   Let $X$ be any domain and $Y$ any label set, possibly infinite, and let $\mathcal G\subseteq Y^X$ be learnable in the sense of §2: some learner $A$ has, for every $\varepsilon,\delta\in(0,1)$, a sample size $n_A(\varepsilon,\delta)$ with $\Pr_{S\sim D^m}[L_D(A(S),h^\star)>\varepsilon]\le\delta$ for all $m\ge n_A(\varepsilon,\delta)$, all $h^\star\in\mathcal G$ and all distributions $D$ on $X$. Then
--   $$\mathrm{DS}(\mathcal G)<\infty .$$
--
--   The proof of Theorem 3.1 (p. 18) uses this fact for $\mathcal G=\mathcal H_{\mathrm{prop}}$: "$\mathrm{DS}(\mathcal H_{\mathrm{prop}})=\infty$, which contradicts the fact that $\mathcal H_{\mathrm{prop}}$ is learnable". It is the necessity half of the characterization of multiclass learnability by the DS dimension recalled on p. 4 ("learnability amounts to finiteness of the DS dimension [BCD+22, Pab26]"); the sufficiency half is not used by Theorem 3.1 and is not part of this item. The label set is arbitrary: with infinitely many labels the Natarajan dimension does not characterize learnability, and the DS dimension is the right quantity.
--
--   **Formalization Note.** $\mathrm{DS}$ is `MulticlassDS.Compress.dsDim` (`ℕ∞`) and $<\infty$ is `< ⊤`. `PACLearnable` is the §2 notion of the definition `PAC` (σ-algebra `⊤` on $X$, one deterministic learner, one sample-size function).
--
--   Differences from the source:
--   - encoding: distributions on an arbitrary X and P_{S∼D^m}[·] → probability measures for the σ-algebra ⊤ and the `Measure.pi` product measure, which on a bad set that is not product-measurable (possible only for uncountable X) is its outer measure; reason: the paper fixes no σ-algebra; on countable X, and for every finitely supported D, this is the ordinary probability
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18, §3.1 ("contradicts the fact that Hprop is learnable"), citing p. 4 [BCD+22, Pab26]

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-- The fact cited on p. 18 (from p. 4, [BCD+22, Pab26]): a PAC learnable class, over any domain
`X` and any label set `Y`, has finite DS dimension. -/
theorem learnable_ds_finite {X Y : Type*} (G : Set (X → Y)) (hG : PACLearnable G) :
    MulticlassDS.Compress.dsDim G < ⊤ := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
