-- Prove2me | Theorems.Thm_DbarRegularity_calderonZygmund_decomposition
-- name    : DbarRegularity.calderonZygmund_decomposition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:52:43.96458+00:00
-- url     : https://prove2.me/theorems/8a5a2330-1eb5-45df-b73b-f4900ae976ad
-- title:
--   The Calderón–Zygmund decomposition of a non-negative integrable function
-- statement:
--   Let $d\ge1$, let $f\ge0$ be an integrable function on $\mathbb{R}^d$ and let $\alpha>0$. $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Then there is a decomposition $\mathbb{R}^d=F\cup\Omega$, $F\cap\Omega=\emptyset$, such that
--
--   1. $f(x)\le\alpha$ for almost every $x\in F$;
--   2. $\Omega=\bigcup_k Q_k$ is a countable union of closed cubes $Q_k$ (with positive side lengths) whose interiors are pairwise disjoint, and for every $k$
--   $$\alpha<\frac{1}{m(Q_k)}\int_{Q_k}f(x)\,dx\le 2^d\alpha .$$
--
--   **Formalization Note** A cube is `closedCube a s` $=\{x: a_i\le x_i\le a_i+s\}$ with $s>0$. The family of cubes is indexed by a countable type `ι`; Stein does not say "countable", but cubes with disjoint interiors are automatically countably many. The average is `(∫ x in Q, f x) / (volume Q).toReal`, where `volume Q` is finite and positive. The hypothesis $d\ge1$ is implicit in Stein: for $d=0$ the space is a point of measure $1$ and the statement fails when $f>\alpha$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter I, § 3.2, Theorem 4, pp. 17–18

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter I, § 3.2, Theorem 4 (p. 17): for a non-negative integrable
`f` on `ℝ^d` (`d ≥ 1`) and `α > 0` there is a decomposition `ℝ^d = F ∪ Ω`, `F ∩ Ω = ∅`, with
`f ≤ α` almost everywhere on `F` and `Ω` a union of closed cubes `Q_k` with pairwise disjoint
interiors such that `α < (1 / |Q_k|) ∫_{Q_k} f ≤ 2^d α` for every `k`. -/
theorem calderonZygmund_decomposition {d : ℕ} (hd : 0 < d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (α : ℝ) (hα : 0 < α) :
    ∃ (F Ω : Set (EuclideanSpace ℝ (Fin d))) (ι : Type) (_ : Countable ι)
      (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      F ∪ Ω = Set.univ ∧ Disjoint F Ω ∧
      (∀ᵐ x, x ∈ F → f x ≤ α) ∧
      Ω = ⋃ k, closedCube (a k) (s k) ∧
      (∀ k, 0 < s k) ∧
      Pairwise (fun k l => Disjoint (interior (closedCube (a k) (s k)))
        (interior (closedCube (a l) (s l)))) ∧
      ∀ k, α < (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal ∧
        (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal
          ≤ 2 ^ d * α := by sorry

end DbarRegularity
