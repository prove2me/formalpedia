-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_3_10
-- name    : AgnGaussTomo.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:48.977208+00:00
-- url     : https://prove2.me/theorems/433e1971-2476-4d90-9d2c-4dc01b4c5087
-- title:
--   Lemma 3.10 — $\|K_\theta\varphi\|_2\le2(m+2)\|\theta\|_{\mathcal P}\|\varphi\|_2$ on $\mathcal F_{\le m}$
-- statement:
--   For every $n$, every $\theta=(b,A)\in\mathcal P_n$, every $m\in\mathbb N$ and every Fock vector $|\varphi\rangle$ in $\mathcal F_{\le m}=\Pi_{\le m}\mathcal F$ (total photon number at most $m$),
--
--   $$
--   \|K_\theta|\varphi\rangle\|_2\le2(m+2)\,\|\theta\|_{\mathcal P}\,\||\varphi\rangle\|_2,\qquad K_\theta=\sum_ib_i\hat a_i^\dagger+\tfrac12\sum_{i,j}A_{ij}\hat a_i^\dagger\hat a_j^\dagger .
--   $$
--
--   This norm growth bound controls the higher derivatives of $\theta\mapsto|\psi(\theta)\rangle$.
--
--   Differences from the source:
--   - encoding: vectors |φ⟩ ∈ F_{≤m} and their ℓ² norms → Fock coefficient families vanishing above total photon number m, with ‖·‖₂ = (Σ_u |φ_u|²)^{1/2}; reason: these vectors are finitely supported, so the series are finite sums
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.10, printed p. 19 (PDF p. 22); proof on pp. 19–20

import Mathlib
import Definitions.Def_AgnGaussTomo_Kop
import Definitions.Def_AgnGaussTomo_LowPhoton

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Lemma 3.10: `K_θ` on the `≤ m`-photon subspace.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.10, printed p. 19
(PDF p. 22): "Let Π_{≤m} be the projector onto states with total photon number at most m. For
|φ⟩ ∈ F_{≤m} ≡ Π_{≤m} F, we have that ‖K_θ |φ⟩‖₂ ≤ 2(m + 2)‖θ‖_P ‖|φ⟩‖₂."

**Formalization Note.** `θ` is an arbitrary point of `Pspace n` (`K_θ` is defined for every `(b, A)`);
`‖θ‖` is `‖θ‖_P`. Vectors are Fock coefficient families; `‖·‖₂` is `(Σ_m |φ_m|²)^{1/2}` (finite sums,
since `φ` and `K_θ φ` are finitely supported). -/
theorem lemma_3_10 (n : ℕ) (θ : Pspace n) (m : ℕ) (φ : Occupation (Fin n) → ℂ)
    (hφ : LowPhoton m φ) :
    Real.sqrt (∑' u, ‖Kop θ φ u‖ ^ 2) ≤
      2 * ((m : ℝ) + 2) * ‖θ‖ * Real.sqrt (∑' u, ‖φ u‖ ^ 2) := by sorry

end AgnGaussTomo
