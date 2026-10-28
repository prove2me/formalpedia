-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_punctured
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_punctured
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T21:51:43.276347+00:00
-- url     : https://prove2.me/theorems/8654a551-6fb5-4e26-919e-e0d9c78c85c5
-- title:
--   Compactness in C^∞_loc of pseudoholomorphic maps on growing punctured discs
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $O\subset E$ open, and $J$ a smooth almost complex structure on $O$. Let $R_k\to\infty$ and let $v_k$ be smooth $J$-holomorphic maps on the punctured discs $\{0<|z|<R_k\}$. Assume that for every compact $K\subset\mathbb C\setminus\{0\}$ there are a compact $K'\subset O$ and $M$ such that, for all sufficiently large $k$, $v_k(K)\subset K'$ and $\|Dv_k\|\le M$ on $K$. Then a subsequence $v_{k_j}$ converges in $C^\infty_{\mathrm{loc}}(\mathbb C\setminus\{0\})$ to a smooth $J$-holomorphic map $w:\mathbb C\setminus\{0\}\to O$.
--
--   This is the punctured-plane counterpart of `exists_subseq_tendstoCInftyLocOn_univ` (growing discs, limit on $\mathbb C$); it is the compactness statement used for blow-ups of finite-energy curves at a puncture.
--
--   **Formalization Note** "$J$ smooth almost complex structure on $O$" is `JHolomorphic.IsAlmostComplexOn J O` (it includes that $O$ is open). $C^\infty_{\mathrm{loc}}(\mathbb C\setminus\{0\})$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `{z | z ≠ 0}`: uniform convergence of every `iteratedFDeriv` on every compact subset. The maps are functions on all of $\mathbb C$; only their behaviour on `{z | z ≠ 0 ∧ ‖z‖ < R k}` matters. "For all sufficiently large $k$" is `∀ᶠ k in atTop`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Proposition 9.1 and Section 9.2 (punctured-plane form)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness on the punctured plane for pseudoholomorphic maps on growing punctured
discs. Let `J` be a smooth almost complex structure on an open set `O` of a finite-dimensional
real normed space `E`, let `R_k → ∞`, and let `v_k` be smooth and `J`-holomorphic on
`{0 < |z| < R_k}`. Assume that for every compact `K ⊆ ℂ \ {0}` there are a compact `K' ⊆ O` and a
constant `M` such that `v_k(K) ⊆ K'` and `‖Dv_k‖ ≤ M` on `K` for all large `k`. Then a
subsequence converges in `C^∞_loc(ℂ \ {0})` to a smooth `J`-holomorphic map
`w : ℂ \ {0} → O`. -/
theorem exists_subseq_tendstoCInftyLocOn_punctured {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hv : ∀ k, ContDiffOn ℝ ∞ (v k) {z | z ≠ 0 ∧ ‖z‖ < R k})
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0 ∧ ‖z‖ < R k} (v k))
    (hbd : ∀ K ⊆ {z : ℂ | z ≠ 0}, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w {z | z ≠ 0} ∧
      JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0} w ∧ Set.MapsTo w {z | z ≠ 0} O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} := by
  sorry

end FiniteEnergyPlane
