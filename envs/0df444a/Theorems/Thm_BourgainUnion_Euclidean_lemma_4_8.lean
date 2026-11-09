-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_4_8
-- name    : BourgainUnion.Euclidean.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:14.481596+00:00
-- url     : https://prove2.me/theorems/e4ded8f0-f5d1-4d18-b4c5-f0045d5b4393
-- title:
--   Lemma 4.8 — average over the set added last
-- statement:
--   In a finite pseudometric space $X$, let a geometric condition on ambient/subset pairs be preserved by restriction and permit the extension of Lemma 4.7 with fixed factors $t,s\ge1$ for every eligible pair and every $1$-Lipschitz prescribed map. Set $\eta=\max\{t-1,2(s-1)\}$. If $A\ne\varnothing$ and $X\setminus A$ is partitioned into $m$ nonempty sets satisfying the condition, every $1$-Lipschitz map $f:A\to\ell_2$ extends with Lipschitz constant at most
--   $$P_m=\prod_{r=1}^m(1+\eta/r).$$
--   The remaining clauses are
--   $$P_m\le e^\eta(m+1)^\eta,\qquad \eta\ge1\ \Longrightarrow\ P_m\le(m+1)^\eta.$$
--   Thus the first bound is $O((m+1)^\eta)$ for fixed $\eta$, with an explicit $\eta$-dependent constant. For $m=0$ the product is one. These are conditional extension assumptions for this lemma, not extra premises of the goal.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
--   - encoding: a geometric condition preserved by restriction and permitting Lemma 4.7 → predicates on actual ambient/subset pairs, universally tested over all restrictions and all maps; reason: this makes the source condition operational without assuming any global distortion conclusion
--   - generalization: O((m+1)^η) for fixed η → the bound exp(η)(m+1)^η; reason: the explicit constant is supplied by the proof on p. 20; it is not asserted uniform in η; the explicit form implies the source's asymptotic statement
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 19, Lemma 4.8, equation (14)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_AveragingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 4.8: all restricted ambient/subset pairs, P_0=1, and both asymptotic clauses. -/
theorem lemma_4_8 {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (P : Set X → Set X → Prop) (t s : ℝ) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hstable : RestrictionStable P) (hpermit : PermitsExtensions P t s)
    (A : Set X) (hA : A.Nonempty) (m : ℕ) (B : Fin m → Set X)
    (hpart : PartitionComplement A B) (hP : ∀ i, P Set.univ (B i)) :
    let η := max (t-1) (2*(s-1))
    (∀ f : X → H2, LipOn 1 f A → ∃ F : X → H2,
      Set.EqOn F f A ∧ LipOn (productFactor η m) F Set.univ) ∧
    productFactor η m ≤ Real.exp η * (m+1 : ℝ)^η ∧
    (1 ≤ η → productFactor η m ≤ (m+1 : ℝ)^η) := by sorry

end BourgainUnion.Euclidean
