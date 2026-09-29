-- Prove2me | Theorems.Thm_AlgebraicCurve_abs_prox_evalVec_sub_prox_le_of_coordinate_change
-- name    : AlgebraicCurve.abs_prox_evalVec_sub_prox_le_of_coordinate_change
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/a4cf45f9-6d01-534d-8793-04d380089ead
-- title:
--   Chordal proximity under a bounded change of coordinates
-- statement:
--   Let $F$ be a field that is an algebra over $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ`, let $r$ be a natural number and let $s,t : \mathrm{Fin}\,r \to F$ have all entries nonzero. Suppose $M,M'$ are $r\times r$ matrices over $\overline{\mathbb Q}$ with $t_j=\sum_i M_{ji}\cdot s_i$ for all $j$ and $s_i=\sum_j M'_{ij}\cdot t_j$ for all $i$ (scalar action of $\overline{\mathbb Q}$ on $F$). Let $\mu$ be a non-archimedean real-valued absolute value on $\overline{\mathbb Q}$, and let $C\ge 1$ be a real number with $\mu(M_{ji})\le C$ and $\mu(M'_{ij})\le C$ for all indices. Let $P,Q$ be places of $F$ over $\overline{\mathbb Q}$ in the sense of the project's `Place` structure (a valuation subring of $F$, not equal to $\top$, containing the image of $\overline{\mathbb Q}$ and a principal ideal ring), each rational in the sense that $\overline{\mathbb Q}$ surjects onto its residue field; for such places `evalAt` sends an element of the valuation subring to a chosen $\overline{\mathbb Q}$-preimage of its residue, and $0$ otherwise. Let $c_P,c_Q$ be indices with $0\le P.\mathrm{ord}(t_j t_{c_P}^{-1})$ and $0\le Q.\mathrm{ord}(t_j t_{c_Q}^{-1})$ for all $j$, where $\mathrm{ord}$ is minus the logarithm of the associated adic valuation. Write $x(P)=$ `evalVec s P`, the vector with $j$-th entry $P.\mathrm{evalAt}(s_j s_{\iota}^{-1})$, $\iota$ being an index of least $P.\mathrm{ord}$ among the $s_i$ (and $0$ if $r=0$), and similarly $x(Q)$. Assume $x(P)$ and $x(Q)$ are not proportional, i.e. $x(P)_i x(Q)_j \ne x(P)_j x(Q)_i$ for some $i,j$. Then, with $$\mathrm{prox}_\mu(u,v)=\log\sup_i \mu(u_i)+\log\sup_j \mu(v_j)-\log\sup_{i,j}\mu(u_i v_j-u_j v_i),$$ one has $\bigl|\mathrm{prox}_\mu(x(P),x(Q))-\mathrm{prox}_\mu\bigl((P.\mathrm{evalAt}(t_j t_{c_P}^{-1}))_j,(Q.\mathrm{evalAt}(t_j t_{c_Q}^{-1}))_j\bigr)\bigr|\le 4\log C$.
--
--   This is the metric comparison showing that the chordal proximity of two rational points, computed in two coordinate models of a curve whose coordinate systems are related by matrices with $\mu$-bounded entries, changes by at most $4\log C$; the normalising factors at the two pivots cancel in the proximity. It is used in the construction of uniformly adapted bases, [`ModularCurve.exists_uniform_adapted_basis`](thm.html#ModularCurve.exists_uniform_adapted_basis), where $C$ is a power of $\mu(p)^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_abs_prox_evalVec_sub_prox_le_of_coordinate_change.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.abs_prox_evalVec_sub_prox_le_of_coordinate_change
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ j, t j ≠ 0)
    (M M' : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ))
    (hM : ∀ j, t j = ∑ i, M j i • s i) (hM' : ∀ i, s i = ∑ j, M' i j • t j)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (C : ℝ) (hC : 1 ≤ C) (hMC : ∀ j i, μ (M j i) ≤ C) (hM'C : ∀ i j, μ (M' i j) ≤ C)
    (P Q : Place (AlgebraicClosure ℚ) F) (hP : P.IsRational) (hQ : Q.IsRational)
    (cP cQ : Fin r)
    (hcP : ∀ j, 0 ≤ P.ord (t j * (t cP)⁻¹)) (hcQ : ∀ j, 0 ≤ Q.ord (t j * (t cQ)⁻¹))
    (hne : ∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) :
    |prox (μ : AlgebraicClosure ℚ → ℝ) (evalVec s P) (evalVec s Q)
        - prox (μ : AlgebraicClosure ℚ → ℝ) (fun j => P.evalAt (t j * (t cP)⁻¹))
            (fun j => Q.evalAt (t j * (t cQ)⁻¹))|
      ≤ 4 * Real.log C := by sorry
