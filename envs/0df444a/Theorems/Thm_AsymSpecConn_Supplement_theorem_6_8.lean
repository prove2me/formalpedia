-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_6_8
-- name    : AsymSpecConn.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:26:09.453036+00:00
-- url     : https://prove2.me/theorems/efc74f7e-921c-4a17-9472-c873f5893c9d
-- title:
--   Theorem 6.8 — maximality of the non-crossing upper quantum functional
-- statement:
--   Let $B$ be a non-crossing family of bipartitions, let $\theta\in\mathcal P(B)$ and let $w_\theta=\prod_bR_b^{\theta(b)}$. Then the non-crossing upper quantum functional $F^\theta$ is a spectral point, is itself dominated by $w_\theta$, pointwise dominates every spectral point dominated by $w_\theta$, and equals the repeated interpolant for every allowed enumeration.
--
--   Thus Lean states spectrality, the full largest-element property (including membership in the dominated set), and enumeration-independent equality.
--
--   Differences from the source:
--   - generalization: the source distinguishes the last leg $k$ → Lean permits any distinguished root leg; reason: choosing the last `Fin k` element specializes exactly to the source, and relabelling legs gives every other case
--   - encoding: partitions and isotypic projectors are written abstractly as $\lambda\vdash n$ and $P^b_\lambda$ → Lean uses padded labelled Young diagrams, Young-symmetrizer Specht characters, and the displayed character projector formula; reason: cell labelling only conjugates the construction and changes no projector or entropy value
--   - encoding: abstract tensor legs and quotient classes → Lean evaluates chosen bases and a chosen quotient representative; reason: simultaneous isotypic support and its entropy supremum are invariant under invertible basis changes and unused ambient directions
--   - encoding: the repeated interpolant is a recursive prose construction → Lean identifies every function carrying the exact stage witness with $F^\theta$; reason: Theorem 6.6 supplies such a function for every allowed enumeration, so the equality is non-vacuous and refers only to the source construction
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 6.8, p.49

import Mathlib
import Definitions.Def_AsymSpecConn_Supplement_nonCrossingUpperQuantum

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn.Supplement

/-- **Theorem 6.8** (p.49) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): the non-crossing upper quantum functional is spectral, is itself dominated by
the weighted flattening-rank product and pointwise dominates every spectral point with that
property, and equals the repeated interpolant for every allowed enumeration.

**Formalization Note** `nonCrossingUpperQuantum` is the §6.7 supremum over simultaneous
isotypic projections, using the character formula displayed on p.48.  Partitions are padded by
zeroes and represented by labelled Young diagrams; their Specht characters, and hence the
projectors, do not depend on the cell labels.  The arbitrary `root` convention generalizes the
source's choice of the last leg and specializes to it. -/
theorem theorem_6_8 {k : ℕ} (hk : 2 ≤ k) (root : Fin k)
    (B : Finset (Bipartition k root)) (hB : NonCrossing B) (θ : ↑B → ℝ)
    (hθ : IsProbabilityWeight θ) :
    let F := nonCrossingUpperQuantum B θ
    let w := nonCrossingRankWeight B θ
    F ∈ AsymSpecConn.Spectrum (MME.TensorQ ℂ k) (AsymSpecConn.tensorPreorder ℂ hk) ∧
    (∀ s, F s ≤ w s) ∧
    (∀ g ∈ AsymSpecConn.Spectrum (MME.TensorQ ℂ k) (AsymSpecConn.tensorPreorder ℂ hk),
      (∀ s, g s ≤ w s) → ∀ s, g s ≤ F s) ∧
    ∀ (e : AllowedEnumeration B θ) (f : MME.TensorQ ℂ k → ℝ≥0),
      IsRepeatedInterpolant hk B θ e f → f = F := by sorry

end AsymSpecConn.Supplement
