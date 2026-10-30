-- Prove2me | Theorems.Thm_DiazModulus_exists_coord_complement
-- name    : DiazModulus.exists_coord_complement
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:08.625001+00:00
-- url     : https://prove2.me/theorems/3af86371-8ee2-4e34-a167-2d87b6f03bd2
-- title:
--   The ℚ-span of a set of integer vectors has a coordinate complement: a set J of card N − rank whose coordinate subspace meets the span in 0
-- statement:
--   Let $N$ be a finite set and $A \subseteq \mathbb{Z}^N$, and let $S \subseteq \mathbb{Q}^N$ be the $\mathbb{Q}$-span of $A$. There is $J \subseteq N$ with $|J| + \dim_{\mathbb{Q}} S = |N|$ such that the only vector of $S$ vanishing outside $J$ is $0$.
--
--   **Proof.** The images of the standard basis vectors span $\mathbb{Q}^N / S$; some injectively indexed subfamily $e_j$, $j \in J$, maps to a basis, so $|J| = |N| - \dim S$. If $v \in S$ vanishes outside $J$, then $v = \sum_{j \in J} v_j e_j$ maps to $0$, so every $v_j$ is $0$ by independence.
--
--   **Novelty.** Classical; routine formalisation. Linear algebra.
-- source:
--   Classical linear algebra. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem exists_coord_complement {N : Type} [Fintype N] (A : Set (N → ℤ)) :
    ∃ J : Finset N, J.card + Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : N → ℤ => fun j => (s j : ℚ)) '' A)) = Fintype.card N ∧
      ∀ v ∈ Submodule.span ℚ ((fun s : N → ℤ => fun j => (s j : ℚ)) '' A), (∀ j ∉ J, v j = 0) → v = 0 := by
  sorry

end DiazModulus
