-- Prove2me | Theorems.Thm_CubicPermFPRAS_proposition_16
-- name    : CubicPermFPRAS.proposition_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:56.613294+00:00
-- url     : https://prove2.me/theorems/c618ce80-c537-4c18-9543-31193be7ea26
-- title:
--   Proposition 16, p.14 — $\Pr[Q_T>C_\alpha n(1+\sqrt a)(T+\log 2n)^2]\le e^{-T}$ from a 3-warm start
-- statement:
--   For every $\alpha>1$ and $J_\alpha\ge8\alpha^2$ there is a constant $C_\alpha>0$ such that, under the standing assumptions of §8.1, for every $a\in[1/n,J]$, every $T\ge0$ and every 3-warm start $\xi$ for $\nu_a$, the number $Q_T$ of resampling events up to time $T$ satisfies
--   $$\Pr\Big[Q_T>C_\alpha n(1+\sqrt a)\big(T+\log(2n)\big)^2\Big]\le e^{-T}.$$
--
--   Differences from the source:
--   - encoding: $\Pr[Q_T>x]$ from $\sigma\sim\xi$ → $\sum_\sigma\xi(\sigma)\Pr_\omega[\text{the simulation with limit }\lfloor x\rfloor\text{ observes more than }\lfloor x\rfloor\text{ events}]$; reason: $Q_T$ is an integer, and the limited simulation detects exactly whether $Q_T>\lfloor x\rfloor$
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Proposition 16, p.14 (PDF 16); proof in §8.4, pp.50–53 (PDF 52–55)

import Mathlib
import Definitions.Def_CubicPermFPRAS_sampler

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Proposition 16** (few resamplings from a warm start), p.14 (PDF 16), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); proved in
§8.4 (pp.50–53).

There is a constant `C_α > 0`, depending only on `α`, such that, for every `a ∈ [1/n, J]` and
`T ≥ 0`, from any 3-warm start for `ν_a`,
`Pr[Q_T > C_α n(1 + √a)(T + log(2n))²] ≤ e^{−T}`.

**Formalization Note.** `Q_T` is the number of resampling events up to time `T`; since it is an
integer, `Q_T > x` iff `Q_T > ⌊x⌋`, and the stage simulation with limit `R = ⌊x⌋` observes
exactly whether `Q_T > R` (its ring count exceeds `R`). The start is `σ ∼ ξ`; the probability is
`∑_σ ξ(σ) Pr_ω[Q_T > R from σ]`. The §8.1 standing assumptions (p.37) are the binders. -/
theorem proposition_16 : ∀ α : ℝ, 1 < α → ∀ Jα : ℝ, 8 * α ^ 2 ≤ Jα → ∃ Cα : ℝ, 0 < Cα ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w →
    ∀ a : ℝ, 1 / (n : ℝ) ≤ a → a ≤ Jα * (n : ℝ) ^ 2 → ∀ T : ℝ, 0 ≤ T →
    ∀ ξ : Asg n → ℝ, IsWarm3 ξ (nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) a) →
      ∑ σ, ENNReal.ofReal (ξ σ) *
          tapeMeasure {ω | ⌊Cα * n * (1 + Real.sqrt a) * (T + Real.log (2 * n)) ^ 2⌋₊ <
            (runFree (stage (Bmat lam w) (Jα * (n : ℝ) ^ 2) a T
              ⌊Cα * n * (1 + Real.sqrt a) * (T + Real.log (2 * n)) ^ 2⌋₊ σ) ω).1.2} ≤
        ENNReal.ofReal (Real.exp (-T)) := by sorry

end CubicPermFPRAS
