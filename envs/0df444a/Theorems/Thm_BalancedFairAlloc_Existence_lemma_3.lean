-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_3
-- name    : BalancedFairAlloc.Existence.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:52.706849+00:00
-- url     : https://prove2.me/theorems/0de8d201-68d3-4730-9434-4d1018089aec
-- title:
--   Lemma 3 — regularized selection: the unique minimizer of f(w,·)+λ‖·‖² over K(w) is continuous in w, with objective gap at most λC
-- statement:
--   Let $P\subseteq\mathbb R^k$ be compact and let $K$ assign to every $w\in P$ a nonempty compact convex set $K(w)\subseteq\mathbb R^d$, all contained in one fixed compact set $B$, such that $K$ has a closed graph and is lower hemicontinuous on $P$. Let $f(w,z)$ be jointly continuous on $P\times\mathbb R^d$ and convex in $z$, and let $\lambda>0$. Then for every $w\in P$ the function $z\mapsto f(w,z)+\lambda\|z\|_2^2$ has a unique minimizer $z_\lambda(w)$ over $K(w)$, and $w\mapsto z_\lambda(w)$ is continuous on $P$. Moreover, if $K(w)$ contains an exact minimizer $z^*(w)$ of $f(w,\cdot)$ with $\|z^*(w)\|_2^2\le C$, then
--
--   $$f\big(w,z_\lambda(w)\big)\le\min_{z\in K(w)}f(w,z)+\lambda C.$$
--
--   The lemma is applied to the regularized dual (10): it makes the dual prices $p^\lambda(w)$ unique and continuous in $w$, at an objective cost of at most $\lambda C_D$ (eq. (11)).
--
--   Differences from the source:
--   - reading: K continuous, nonempty, compact convex-valued on a compact parameter space; f continuous and convex in z → P ⊆ ℝ^k compact; K(w) nonempty, compact, convex for w ∈ P; closed graph and lower hemicontinuity on P; K(w) ⊆ B for one compact B; f jointly continuous on P × ℝ^d and convex in z for w ∈ P; reason: these are the precise hypotheses Appendix C states ('We first make the hypotheses precise'), including the fixed compact box it assumes
--   - generalization: one fixed compact box B → any compact set B; reason: a box is a compact set; the statement specializes to the printed one
--   - reading: the unique minimizer is continuous in w → a map z_λ that at every w ∈ P is a minimizer, is the only one, and is continuous on P; reason: existence and uniqueness are the first part of the proof in Appendix C and are what makes 'the unique minimizer' meaningful
--   - generalization: K(w) contains an exact minimizer with ‖z*(w)‖² ≤ C uniformly; gap at most λC → for every C and every w ∈ P at which K(w) contains a minimizer z* of f(w,·) with ∑ z*_l² ≤ C, f(w, z_λ(w)) ≤ f(w, y) + λC for all y ∈ K(w); reason: pointwise in w; the uniform hypothesis gives it at every w, and the conclusion is App. C's display f(w, z_λ(w)) ≤ min_K f(w,·) + λC
--   - encoding: ‖z‖₂² → ∑_l z_l ^ 2; reason: same quantity
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 11 (PDF 13), Lemma 3; hypotheses made precise in Appendix C, p. 56 (PDF 58)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Correspondence

namespace BalancedFairAlloc.Existence

theorem lemma_3 (k d : ℕ) (P : Set (Fin k → ℝ)) (hP : IsCompact P)
    (K : (Fin k → ℝ) → Set (Fin d → ℝ))
    (hKne : ∀ w ∈ P, (K w).Nonempty) (hKc : ∀ w ∈ P, IsCompact (K w))
    (hKv : ∀ w ∈ P, Convex ℝ (K w))
    (hKgraph : HasClosedGraphOn P K) (hKlhc : IsLowerHemicontinuousOn P K)
    (B : Set (Fin d → ℝ)) (hB : IsCompact B) (hKB : ∀ w ∈ P, K w ⊆ B)
    (f : (Fin k → ℝ) → (Fin d → ℝ) → ℝ)
    (hfc : ContinuousOn (fun q : (Fin k → ℝ) × (Fin d → ℝ) => f q.1 q.2) (P ×ˢ Set.univ))
    (hfv : ∀ w ∈ P, ConvexOn ℝ Set.univ (f w))
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ zlam : (Fin k → ℝ) → (Fin d → ℝ),
      (∀ w ∈ P, zlam w ∈ K w ∧
        (∀ y ∈ K w, f w (zlam w) + lam * ∑ l, zlam w l ^ 2 ≤ f w y + lam * ∑ l, y l ^ 2) ∧
        (∀ z ∈ K w, (∀ y ∈ K w, f w z + lam * ∑ l, z l ^ 2 ≤ f w y + lam * ∑ l, y l ^ 2) →
          z = zlam w)) ∧
      ContinuousOn zlam P ∧
      (∀ C : ℝ, ∀ w ∈ P,
        (∃ zs ∈ K w, (∀ y ∈ K w, f w zs ≤ f w y) ∧ ∑ l, zs l ^ 2 ≤ C) →
        ∀ y ∈ K w, f w (zlam w) ≤ f w y + lam * C) := by sorry

end BalancedFairAlloc.Existence
