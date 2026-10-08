-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_zero_iff_resolvent_fixed
-- name    : DouglasRachfordPPA.GenDR.zero_iff_resolvent_fixed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:22:59.27823+00:00
-- url     : https://prove2.me/theorems/a54e445b-bd7a-4102-b06d-c447b6f90fc3
-- title:
--   Lemma 2 — $0\in Tx$ iff $J_{cT}(x)=x$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $T$ a maximal monotone operator on $\mathcal H$, $c>0$ and $x\in\mathcal H$. Then
--   $$0\in Tx\iff J_{cT}(x)=x .$$
--
--   The zeros of a maximal monotone operator are exactly the fixed points of its resolvents; this is what makes the proximal point iteration $z^{k+1}=J_{c_kT}(z^k)$ a method for finding zeros.
--
--   **Formalization Note** $J_{cT}$ is the graph resolvent `opResolvent c T`. The paper writes $J_{cT}(x)$ for its unique value; the Lean statement says the value set $J_{cT}(x)$ is the singleton $\{x\}$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 9, Lemma 2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Lemma 2: for maximal monotone `T`, `c > 0` and `x ∈ H`, `0 ∈ T x` iff `J_{cT}(x) = x`
(the resolvent is single-valued, so this is `J_{cT} x = {x}` as a set). -/
theorem zero_iff_resolvent_fixed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (c : ℝ) (hc : 0 < c) (x : H) :
    (0 : H) ∈ T x ↔ opResolvent c T x = {x} := by sorry

end DouglasRachfordPPA.GenDR
