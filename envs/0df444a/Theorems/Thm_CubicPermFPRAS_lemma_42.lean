-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_42
-- name    : CubicPermFPRAS.lemma_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:52.220846+00:00
-- url     : https://prove2.me/theorems/f83a742a-c17a-49e8-9cf7-1d95994dc990
-- title:
--   Lemma 42, p.41 — $\mathbb E[n-|M|]\le A_\alpha(1+\min\{n,n/\sqrt a\})$ and the tail of $\mathrm{un}$ under $\nu_a$
-- statement:
--   For every $\alpha>1$ there is a constant $A_\alpha\ge1$, depending only on $\alpha$, such that under the standing assumptions of §8.1, for every $a>0$, a matching $M$ drawn with probability $a^{|M|}B(M)/F(a)$ satisfies
--   $$\mathbb E[n-|M|]\le A_\alpha\Big(1+\min\Big\{n,\frac n{\sqrt a}\Big\}\Big),$$
--   and for every $v\ge0$,
--   $$\nu_a(\mathrm{un}\ge v)\le\frac43\exp\Big[A_\alpha\Big(1+\min\Big\{n,\frac n{\sqrt a}\Big\}\Big)\Big]2^{-v}.$$
--
--   These bounds control the number of unassigned vertices, and hence the number of fast resampling events, at each activity.
--
--   Differences from the source:
--   - encoding: expectation under the law $a^{|M|}B(M)/F(a)$; $\nu_a(\mathrm{un}\ge v)$ → explicit finite sums over matchings and assignments; reason: the same quantities
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 42, p.41 (PDF 43)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 42** (unmatched vertices), p.41 (PDF 43), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

There is a constant `A_α ≥ 1`, depending only on `α`, such that, for every `a > 0`, a matching
`M` drawn with probability `a^{|M|}B(M)/F(a)` satisfies
`E[n − |M|] ≤ A_α(1 + min{n, n/√a})` (45), and for every `v ≥ 0`,
`ν_a(un ≥ v) ≤ (4/3) exp[A_α(1 + min{n, n/√a})] 2^{−v}` (46).

**Formalization Note.** `A_α` is quantified before `n`, the activities, the anchor, the
weights, `J_α` and `a`; the §8.1 standing assumptions (p.37) are the binders. -/
theorem lemma_42 : ∀ α : ℝ, 1 < α → ∃ Aα : ℝ, 1 ≤ Aα ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w →
    ∀ Jα : ℝ, 8 * α ^ 2 ≤ Jα → ∀ a : ℝ, 0 < a →
      meanUnmatched (Bmat lam w) a ≤ Aα * (1 + min (n : ℝ) (n / Real.sqrt a)) ∧
      ∀ v : ℝ, 0 ≤ v →
        ∑ σ ∈ Finset.univ.filter (fun σ : Asg n => v ≤ (un σ : ℝ)),
            nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) a σ ≤
          4 / 3 * Real.exp (Aα * (1 + min (n : ℝ) (n / Real.sqrt a))) * (2 : ℝ) ^ (-v) := by sorry

end CubicPermFPRAS
