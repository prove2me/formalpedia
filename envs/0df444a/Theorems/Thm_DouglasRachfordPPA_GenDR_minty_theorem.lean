-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_minty_theorem
-- name    : DouglasRachfordPPA.GenDR.minty_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:22:09.049144+00:00
-- url     : https://prove2.me/theorems/bd8d2495-8c3b-4fe2-8049-04853ddbfe66
-- title:
--   Theorem 1 (Minty) — a monotone $T$ is maximal iff $\mathrm{im}(I+T)=\mathcal H$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and let $T$ be a monotone operator on $\mathcal H$. Then
--   $$T\ \text{is maximal monotone}\iff \operatorname{im}(I+T)=\mathcal H .$$
--
--   This characterization, due to Minty (1962), converts maximality (a statement about all monotone extensions of $T$) into solvability of the inclusion $z\in x+Tx$ for every $z$. The paper uses it to obtain full domain of resolvents (Theorem 2) and maximality of the splitting operator (Theorem 4).
--
--   **Formalization Note** The operator $T$ is a map `H → Set H`; $I+T$ is the graph sum with the identity, and $\operatorname{im}$ is the projection of the graph on its second coordinate. Completeness of $\mathcal H$ is assumed, as in the paper.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 5, Theorem 1 (quoted from Minty 1962)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 1 (Minty 1962): a monotone operator `T` on a Hilbert space is maximal iff
`im(I + T) = H`. -/
theorem minty_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by sorry

end DouglasRachfordPPA.GenDR
