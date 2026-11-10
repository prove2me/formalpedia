-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_4_1
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:28:58.127204+00:00
-- url     : https://prove2.me/theorems/ba7e45cd-2c63-41ac-bc90-284df87e73db
-- title:
--   Lemma 4.1 — sampling with a revelation flag
-- statement:
--   Let $\mathrm{Info}\sim\mu_I$ on a measurable space, let $B$ be an independent uniform bit, and let $\mathrm{View}\sim\kappa(\mathrm{Info},B)$ for a Markov kernel $\kappa$ (the conditional law $\mathcal L(\mathrm{View}\mid\mathrm{Info},B)$). Suppose $p\in[0,1]$ and $\mathrm{TV}(\kappa(o,0),\kappa(o,1))\le p$ for $\mu_I$-almost every $o$. Then there is a sampler, a Markov kernel $\eta$ receiving $\mathrm{Info}$, an independent Bernoulli($p$) flag $f$ and the bit $f\wedge B$ (so it receives $B$ exactly when the flag is set). Its output $\mathrm{View}'$ makes $(\mathrm{Info},B,\mathrm{View}')$ have the same law as $(\mathrm{Info},B,\mathrm{View})$.
--
--   Differences from the source:
--   - encoding: jointly distributed (B, Info, View) with B uniform and independent of Info → Info ~ μI, independent uniform B, View ~ κ(Info, B) for a Markov kernel κ on general measurable spaces; reason: κ is the conditional law L(View | Info, B) that the hypothesis presupposes; every such joint law has this form
--   - encoding: every feasible value o of Info → μI-almost every o; reason: conditional laws are determined only almost everywhere; the feasible values carry all the mass
--   - encoding: the sampler receives B when the flag is set → η receives (Info, f, f ∧ B); reason: f ∧ B equals B when f is set and is constant otherwise
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 4.1, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Sampling

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 4.1 (sampling with a revelation flag). -/
theorem lemma_4_1 {I V : Type*} [MeasurableSpace I] [MeasurableSpace V]
    (μI : Measure I) [IsProbabilityMeasure μI]
    (κ : Kernel (I × Bool) V) [IsMarkovKernel κ]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hTV : ∀ᵐ o ∂μI, tvMeasure (κ (o, false)) (κ (o, true)) ≤ p) :
    ∃ (η : Kernel (I × Bool × Bool) V) (_ : IsMarkovKernel η),
      flagSamplerLaw μI p η = (μI.prod bitLaw) ⊗ₘ κ := by sorry

end ChoiSemiHonestMPC.OTUpper
