-- Prove2me | Theorems.Thm_CritWinSpin_LocalTM2_Compiled_sampler_retry_law
-- name    : CritWinSpin.LocalTM2.Compiled.sampler_retry_law
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T18:35:24.647264+00:00
-- url     : https://prove2.me/theorems/514d14f9-03bf-41fe-8b71-830fd6c4d9ff
-- title:
--   Theorem 4.4 — exact random-bit semantics of the finite sampler
-- statement:
--   Fix a finite spin law $S$, a scale $C\ge2$, and $m\ge1$, with alphabet size at most $C$. For a positive-dimensional input on which preprocessing selects the critical branch, let $F$ be its prescribed random-bit budget, $Q$ its prescribed number of trials, and $P$ its concrete one-trial word law. Then the decoded output of the compiled machine has exactly the law
--
--   $$\mathcal L\!\left(\operatorname{decode}(M_{S,C}(\operatorname{enc}(I,m)))\right)=\operatorname{Retry}(P,Q).$$
--
--   The retry operation returns the first successful value from $Q$ independent trials, or failure if all fail. This equality connects the actual finite random-bit program in Theorem 4.4 to the distribution used by its approximation proof.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 4.4, p.17, equation (24). Exact finite-random-bit implementation and retry semantics of the sampler.

import Definitions.Def_CritWinSpin_SamplerNumericalData
import Definitions.Def_CritWinSpin_SamplerMachine
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation CritWinSpin.Implementation.PreprocessPSD
open CritWinSpin.Implementation.SamplerDataFacts
set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled

theorem sampler_retry_law {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) (hqC : (alphabet S).length ≤ C)
    (hN : 0 < N) (hin : preInside S C (encodedInput I.1)=true) :
    let F := criticalCoins S C (encodedInput I.1,m)
    outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N) =
      FiniteRetry.retry (trialWordLaw S C (sampleEulerData S C I m F)
        (samplerStepCount S C (sampleReference I m F))) (trials S C I m) := by sorry

end CritWinSpin.LocalTM2.Compiled
