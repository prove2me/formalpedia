-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_6_6
-- name    : AsymSpecConn.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:25:25.425212+00:00
-- url     : https://prove2.me/theorems/d99464ec-0a81-4963-8c5b-896dc7f5f3af
-- title:
--   Theorem 6.6 — repeated interpolation for non-crossing bipartitions
-- statement:
--   Let $B$ be a non-crossing family of bipartitions and let $\theta\in\mathcal P(B)$. For $b\in B$, let $S_b$ be the part not containing the distinguished last leg and put $w_\theta=\prod_bR_b^{\theta(b)}$. For every allowed enumeration, there is a repeated interpolant $f_\theta$ produced by the construction of §6.5, and it satisfies all three conclusions
--
--   $$
--   f_\theta\in\Delta,\qquad f_\theta\le w_\theta,\qquad
--   f_\theta=w_\theta\ \text{on }\bigcap_{b\in B}A_{S_b}.
--   $$
--
--   Differences from the source:
--   - generalization: the source distinguishes the last leg $k$ → Lean permits any distinguished root leg; reason: choosing the last `Fin k` element specializes exactly to the source, and relabelling legs gives every other case
--   - generalization: the source chooses an allowed enumeration before naming $f_\theta$ → Lean states existence and all three conclusions for every allowed enumeration; reason: the construction and proof on pp.46–47 are uniform in any enumeration satisfying the stated order
--   - encoding: $f_\theta$ is introduced by a recursive prose construction → Lean uses an existential stage witness containing the exact common refinements, merge maps, normalized weights, and $F_w$ equations; reason: this pins down precisely the constructed outputs without quantifying over an arbitrary function
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 6.6, p.47

import Mathlib
import Definitions.Def_AsymSpecConn_Supplement_nonCrossing

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn.Supplement

/-- **Theorem 6.6** (p.47) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): for every allowed enumeration of a non-crossing family, its repeated
interpolant is a spectral point, is dominated by the weighted product of bipartition flattening
ranks, and agrees with that product on the complete intersection of the `S_b`-irreducible sets.

**Formalization Note** An unordered bipartition is encoded by its unique side not containing
`root`; taking `root` arbitrary generalizes the source's distinguished last leg and specializes to
it. `IsRepeatedInterpolant` contains the complete construction of §6.5: exact common refinements,
partial merge maps, normalized weights, and every `F_w` step.  The conclusion quantifies over all
allowed enumerations; the source chooses one, and the same proof applies to each choice. -/
theorem theorem_6_6 {k : ℕ} (hk : 2 ≤ k) (root : Fin k)
    (B : Finset (Bipartition k root)) (hB : NonCrossing B) (θ : ↑B → ℝ)
    (hθ : IsProbabilityWeight θ) :
    ∀ e : AllowedEnumeration B θ,
      ∃ f : MME.TensorQ ℂ k → ℝ≥0,
        IsRepeatedInterpolant hk B θ e f ∧
        f ∈ AsymSpecConn.Spectrum (MME.TensorQ ℂ k) (AsymSpecConn.tensorPreorder ℂ hk) ∧
        (∀ s, f s ≤ nonCrossingRankWeight B θ s) ∧
        ∀ s, (∀ b : ↑B, SubsetIrreducible b.1 s) →
          f s = nonCrossingRankWeight B θ s := by sorry

end AsymSpecConn.Supplement
