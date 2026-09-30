-- Prove2me | Theorems.Thm_ComputationalLearning_vc_eps_net_failure_bound
-- name    : ComputationalLearning.vc_eps_net_failure_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-28T23:15:58.146382+00:00
-- url     : https://prove2.me/theorems/d2a1658f-3ba9-4939-85dc-541eb098e2a3
-- title:
--   Epsilon-net failure bound via double sampling for VC classes
-- statement:
--   Let H be a class of {0,1}-valued functions on a measurable space X with VC dimension at most d, well-behaved for the target concept c (so the double-sample event is null-measurable). For 0 < ε < 1, m ≥ 8/ε, and any probability distribution D on X, the probability under the labeled sample law that a random sample of m examples labeled by c fails to be an ε-net for the error regions {x : h(x) ≠ c(x)}, h ∈ H, is at most 2·Φ_d(2m)·2^(−εm/2), where Φ_d is the shatter coefficient. This is the symmetrization (ghost sample / random swap) estimate at the heart of the Kearns–Vazirani proof of Theorems 3.3–3.4 (An Introduction to Computational Learning Theory, §3.5, pp. 61–62); combined with the polynomial bound Φ_d(2m) ≤ (2em/d)^d it yields the Blumer–Ehrenfeucht–Haussler–Warmuth sample complexity and PAC learnability.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, §3.5 (pp. 61–62)

import Definitions.Def_ComputationalLearning_VC
set_option autoImplicit false

namespace ComputationalLearning

/-- **Epsilon-net failure bound via double sampling** (Kearns–Vazirani, *An Introduction to
Computational Learning Theory*, §3.5, pp. 61–62). If `H` has VC dimension at most `d` and is
well-behaved for the target `c`, then for `m ≥ 8/ε` a random labeled sample of size `m` fails
to be an ε-net for the error regions with probability at most `2 Φ_d(2m) 2^{−εm/2}`. This is
the deep input (symmetrization / ghost-sample / random-swap argument) behind
`ComputationalLearning.vc_sample_bound`; the remainder of that theorem (consistent-learner
reduction, explicit Blumer–Ehrenfeucht–Haussler–Warmuth sample complexity, PAC learnability)
follows by elementary reduction from this bound. -/
theorem vc_eps_net_failure_bound {X : Type} [MeasurableSpace X]
    (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h)
    (d : ℕ) (hd : vcDim H ≤ d)
    (c : X → Bool) (hc : Measurable c) (hwb : IsWellBehaved H c)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (m : ℕ) (hm : 8 / ε ≤ (m : ℝ)) :
    sampleLaw D c m {S | ¬ IsEpsNet H c D ε (samplePoints S)} ≤
      ENNReal.ofReal (2 * (Phi d (2 * m) : ℝ) * (2 : ℝ) ^ (-(ε * (m : ℝ) / 2))) := by
  sorry

end ComputationalLearning
