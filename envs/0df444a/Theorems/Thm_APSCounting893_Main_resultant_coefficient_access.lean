-- Prove2me | Theorems.Thm_APSCounting893_Main_resultant_coefficient_access
-- name    : APSCounting893.Main.resultant_coefficient_access
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:27:19.289918+00:00
-- url     : https://prove2.me/theorems/d1cd8656-dc6f-41fa-bb1e-a064b3660cbe
-- title:
--   Theorem 6.4 — Uniform CH access to resultant coefficient bits
-- statement:
--   For every reduced rational circuit input of length $L$ and every integer tuple $\theta$ of projection, line and form coefficients, let $R_\theta$ be the actual circuit-derived resultant. There is one family of rational representations $a/b$ with $b>0$ whose sign, numerator-magnitude and denominator bit language lies at one fixed level of $\mathrm{CH}$. For every fixed polynomial bound $q$ on the encoded length of $\theta$, one uniform polynomial $p$ satisfies
--
--   $$\deg R_\theta\le2^{p(L)},\qquad\operatorname{bits}(a),\operatorname{bits}(b)\le2^{p(L)}\quad\text{whenever }|\operatorname{enc}(\theta)|\le q(L).$$
--
--   No reduction to lowest terms is required, and unsuccessful geometric parameter choices remain included. The representations are existential outputs, not an assumed coefficient oracle.
--
--   Differences from the source:
--   - generalization: sampled integer parameter tuples of polynomial bit length → all integer tuples for coefficient correctness and bit access, with one exponential bound for each fixed polynomial tuple-length bound; reason: contains every tuple in every source sampling grid and makes the uniformity quantifiers explicit
--   - encoding: the represented rational coefficient of the resultant → integer numerator and positive denominator whose quotient in the complex coefficient field equals the actual coefficient; reason: avoids imposing a reduced-fraction requirement absent from the source
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 6.4, p. 25, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_SampledResultant

set_option autoImplicit false

namespace APSCounting893.Main

theorem resultant_coefficient_access :
    ∃ rho : (I : ReducedCircuit) → SampleTuple I → (Fin 4 →₀ ℕ) → ℤ × ℕ,
      InCountingHierarchy (SampledCoefficientBitLanguage rho) ∧
      (∀ (I : ReducedCircuit) (theta : SampleTuple I) (e : Fin 4 →₀ ℕ),
        0 < (rho I theta e).2 ∧ (sampledResultant I theta).coeff e =
          ((rho I theta e).1 : ℂ) / ((rho I theta e).2 : ℂ)) ∧
      ∀ a b : ℕ, ∃ c d : ℕ, ∀ (I : ReducedCircuit) (theta : SampleTuple I),
        (encodeList encodeInt (List.ofFn theta)).length ≤ polyBound a b I.C.encode.length →
        (sampledResultant I theta).totalDegree ≤ 2 ^ polyBound c d I.C.encode.length ∧
        ∀ e : Fin 4 →₀ ℕ,
          (rho I theta e).1.natAbs.bits.length ≤ 2 ^ polyBound c d I.C.encode.length ∧
          (rho I theta e).2.bits.length ≤ 2 ^ polyBound c d I.C.encode.length := by sorry

end APSCounting893.Main
