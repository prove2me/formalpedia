-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_4_2
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:01.751585+00:00
-- url     : https://prove2.me/theorems/f4aad91e-2c2d-4ade-b9cb-13f4d8d4afce
-- title:
--   Lemma 4.2 — sequential revelation flags
-- statement:
--   Let $\mathrm{Info}\sim\mu_I$, let $D\sim\kappa_D(\mathrm{Info})$, and let $B_1,\dots,B_K$ be independent uniform bits independent of $(\mathrm{Info},D)$; in particular $D$ is independent of the bits given Info. For $i=1,\dots,K$ let $\mathrm{View}_i\sim\mu_i(\mathrm{Info},D,\mathrm{View}_{<i},B_i)$, where the Markov kernel $\mu_i$ depends on the views only through $\mathrm{View}_{<i}$. Fix $p\in[0,1]$ and assume $\mathrm{TV}(\mu_i(o,d,v_{<i},0),\mu_i(o,d,v_{<i},1))\le p$ for almost every $(o,d,v_{<i})$ under its law. Then there is a sampler, a Markov kernel receiving Info, independent Bernoulli($p$) flags, and $B_i$ for each set flag $i$, that generates $(D,\mathrm{View}_1,\dots,\mathrm{View}_K)$ with the same joint law with Info and all hidden bits.
--
--   Differences from the source:
--   - encoding: L(View_i | Info, D, View_<i, B_1..B_K) = μ_{i,Info,D,View<i,B_i}, D independent of the bits given Info → the joint law is seqViewLaw: D ~ κD(Info), independent uniform bits, View_i ~ μ_i(Info, D, views, B_i) with μ_i depending only on views before i (hypothesis hprefix); reason: this is the displayed factorization written with kernels
--   - encoding: View_1, …, View_K further random variables → views in one nonempty measurable space V; reason: views in different spaces embed into their disjoint union; a probability law on an empty space does not exist
--   - encoding: for every feasible (o, d, View<i) → for almost every (o, d, View<i) under the law at step i; reason: conditional laws are determined only almost everywhere
--   - encoding: a sampler that receives Info and the flags and generates (D, Views) → a Markov kernel η from (Info, flags with flag-revealed bits) to (D, Views); reason: any randomized procedure with these inputs is such a kernel
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 4.2, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Sampling

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 4.2 (sequential flags). -/
theorem lemma_4_2 {I D V : Type*} [MeasurableSpace I] [MeasurableSpace D] [MeasurableSpace V]
    [Nonempty V] {K : ℕ} (μI : Measure I) [IsProbabilityMeasure μI]
    (κD : Kernel I D) [IsMarkovKernel κD]
    (μs : Fin K → Kernel (I × D × (Fin K → V) × Bool) V) [∀ i, IsMarkovKernel (μs i)]
    (hprefix : ∀ (i : Fin K) (o : I) (d : D) (v v' : Fin K → V) (b : Bool),
      (∀ j, j < i → v j = v' j) → μs i (o, d, v, b) = μs i (o, d, v', b))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hTV : ∀ i : Fin K, ∀ᵐ y ∂(seqViewLaw μI κD μs i.1),
      tvMeasure (μs i (y.1.1, y.1.2.2, y.2, false)) (μs i (y.1.1, y.1.2.2, y.2, true)) ≤ p) :
    ∃ (η : Kernel (I × (Fin K → Bool × Bool)) (D × (Fin K → V))) (_ : IsMarkovKernel η),
      (((μI.prod (bitsLaw K)).prod (flagsLaw K p)) ⊗ₘ
          (η.comap revealVec measurable_revealVec)).map (fun x => ((x.1.1.1, x.1.1.2), x.2)) =
        (seqViewLaw μI κD μs K).map (fun y => ((y.1.1, y.1.2.1), (y.1.2.2, y.2))) := by sorry

end ChoiSemiHonestMPC.OTUpper
