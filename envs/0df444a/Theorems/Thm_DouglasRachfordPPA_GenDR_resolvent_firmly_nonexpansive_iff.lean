-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_resolvent_firmly_nonexpansive_iff
-- name    : DouglasRachfordPPA.GenDR.resolvent_firmly_nonexpansive_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:22:34.495649+00:00
-- url     : https://prove2.me/theorems/95df58b0-f123-4954-98d4-9c3732a67258
-- title:
--   Theorem 2 — $T$ is (maximal) monotone iff $J_{cT}$ is firmly nonexpansive (with full domain)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $c>0$, and $T$ an operator on $\mathcal H$, with resolvent $J_{cT}=(I+cT)^{-1}$. Then
--
--   1. $T$ is monotone if and only if $J_{cT}$ is firmly nonexpansive;
--   2. $T$ is maximal monotone if and only if $J_{cT}$ is firmly nonexpansive and $\operatorname{dom}(J_{cT})=\mathcal H$.
--
--   The theorem establishes the exact correspondence between (maximal) monotone operators and (full-domain) firmly nonexpansive operators, which is the basis of the paper's analysis of the proximal point algorithm and of Douglas–Rachford splitting.
--
--   **Formalization Note** $J_{cT}$ is the graph resolvent `opResolvent c T`, which need not be single-valued or everywhere defined a priori, and firm nonexpansiveness is the graph notion; the full-domain condition is therefore a separate clause, as in the paper.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 7, Theorem 2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 2: for `c > 0`, `T` is monotone iff its resolvent `J_{cT} = (I + cT)⁻¹` is firmly
nonexpansive, and `T` is maximal monotone iff `J_{cT}` is firmly nonexpansive with
`dom J_{cT} = H`. -/
theorem resolvent_firmly_nonexpansive_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T)) ∧
    (IsMaximalMonotone T ↔
      IsFirmlyNonexpansiveOp (opResolvent c T) ∧ dom (opResolvent c T) = Set.univ) := by sorry

end DouglasRachfordPPA.GenDR
