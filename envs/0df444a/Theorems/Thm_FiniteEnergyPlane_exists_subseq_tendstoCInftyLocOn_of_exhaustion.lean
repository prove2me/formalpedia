-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_exhaustion
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_exhaustion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:33.335132+00:00
-- url     : https://prove2.me/theorems/6ea6e6ce-76f7-44c3-b8fc-cd9c4c918ea6
-- title:
--   $C^\infty_{loc}$ compactness of pseudoholomorphic maps on an exhaustion of the punctured plane
-- statement:
--   Let $J$ be a smooth almost complex structure on an open set $O$ of a finite-dimensional real normed space $E$. Let $D_k\subset\mathbb{C}$ be open sets, increasing in $k$, with $\bigcup_k D_k=\mathbb{C}\setminus\{0\}$, and let $v_k$ be smooth $J$-holomorphic maps on $D_k$. Assume that for every compact $K\subset\mathbb{C}\setminus\{0\}$ there are a compact $K'\subset O$ and a constant $M$ such that $v_k(K)\subset K'$ and $\|Dv_k\|\le M$ on $K$ for all large $k$. Then a subsequence converges in $C^\infty_{loc}(\mathbb{C}\setminus\{0\})$ to a smooth $J$-holomorphic map $w:\mathbb{C}\setminus\{0\}\to O$.
--
--   Role: this treats domains of arbitrary shape (for instance exteriors $\{|z|>r_k\}$ with $r_k\to0$), where the sequence is defined only on growing subsets of the punctured plane.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness on the punctured plane for pseudoholomorphic maps on a monotone open
exhaustion. Let `J` be a smooth almost complex structure on an open set `O` of a finite-dimensional
real normed space `E`, let `D_k` be open, increasing, with `⋃ D_k = ℂ \ {0}`, and let `v_k` be smooth
and `J`-holomorphic on `D_k`. Assume that for every compact `K ⊆ ℂ \ {0}` there are a compact
`K' ⊆ O` and a constant `M` such that `v_k(K) ⊆ K'` and `‖Dv_k‖ ≤ M` on `K` for all large `k`. Then
a subsequence converges in `C^∞_loc(ℂ \ {0})` to a smooth `J`-holomorphic map `w : ℂ \ {0} → O`. -/
theorem exists_subseq_tendstoCInftyLocOn_of_exhaustion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (D : ℕ → Set ℂ) (hDo : ∀ k, IsOpen (D k))
    (hDm : Monotone D) (hDu : ⋃ k, D k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → E)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) (D k))
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (D k) (v k))
    (hbd : ∀ K ⊆ {z : ℂ | z ≠ 0}, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w {z | z ≠ 0} ∧
      JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0} w ∧ Set.MapsTo w {z | z ≠ 0} O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} := by
  sorry

end FiniteEnergyPlane
