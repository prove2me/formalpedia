-- Prove2me | Theorems.Thm_DiazModulus_rational_preimage_finrank
-- name    : DiazModulus.rational_preimage_finrank
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:24.590212+00:00
-- url     : https://prove2.me/theorems/202938cb-98c2-4c98-a7e8-0cf385f7396f
-- title:
--   If a d × l complex matrix M has Q̄-free columns and T ⊆ ℂᵈ is any subspace, some rational S ⊆ ℂˡ has MS ⊆ T and dim S = dim_Q̄ (W ∩ T), W the Q̄-span of the columns of M
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a $d \times l$ matrix with complex entries whose $l$ columns are linearly independent over $\overline{\mathbb Q}$ ($Mb \neq 0$ for every non-zero $b \in \mathbb C^l$ with algebraic coordinates), and let $T \subseteq \mathbb C^d$ be any subspace, rational or not. Let $W \subseteq \mathbb C^d$ be the $\overline{\mathbb Q}$-vector space spanned by the columns of $M$. Then there is a rational subspace $S \subseteq \mathbb C^l$ such that $Ms \in T$ for every $s \in S$ and
--   $$\dim_{\mathbb C} S = \dim_{\overline{\mathbb Q}} (W \cap T).$$
-- source:
--   A step of the proof of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 2.1 (pp. 170–171), in DiazModulus.fischler_theorem_2_1: it supplies the subspace S of the conclusion, whose codimension l − dim S is then the term l − dim_Q̄(W ∩ T) of Roy's Th. 4. The statement keeps, as frozen, the hypothesis that the columns of M are Q̄-free; the proof does not use it, and the conclusion holds without it, for every complex matrix M. Proved from DiazModulus.qbar_linearIndependent_complex. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rational_preimage_finrank {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (hker : ∀ b : Fin l → ℂ, (∀ j, b j ∈ Qbar) → M.mulVec b = 0 → b = 0)
    (T : Submodule ℂ (Fin d → ℂ)) :
    ∃ S : Submodule ℂ (Fin l → ℂ),
      Submodule.span ℂ {v : Fin l → ℂ | v ∈ S ∧ ∀ j, v j ∈ Qbar} = S ∧
      (∀ s ∈ S, M.mulVec s ∈ T) ∧
      Module.finrank ℂ ↥S = Module.finrank (↥Qbar)
        ↥(Submodule.span (↥Qbar) (Set.range fun j i => M i j) ⊓ T.restrictScalars (↥Qbar)) := by
  sorry

end DiazModulus
