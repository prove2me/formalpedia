-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
-- name    : AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/f1afe5d6-7c01-5ad3-bb90-7e96301ec9bd
-- title:
--   Evaluation vector of a family equals a scalar times M applied to a normalised family
-- statement:
--   Let $F$ be a field that is an algebra over $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, let $r$ be a positive natural number, and let $s, t \colon \mathrm{Fin}\,r \to F$ be families with $s_i \neq 0$ and $t_j \neq 0$ for all indices. Let $M$ and $\mathrm{Minv}$ be $r \times r$ matrices over $\overline{\mathbb Q}$ which are mutually inverse in both orders, and suppose $s_i = \sum_j M_{ij} \cdot t_j$ for every $i$. Let $P$ be a place of $F$ over $\overline{\mathbb Q}$, that is, a valuation subring of $F$ containing the image of $\overline{\mathbb Q}$, not equal to all of $F$, and a principal ideal ring; assume $P$ is rational, i.e. the map from $\overline{\mathbb Q}$ to the residue field of its valuation subring is surjective. Let $c$ be an index such that $t_j \cdot t_c^{-1}$ lies in the valuation subring of $P$ for every $j$. Then there is $d \in \overline{\mathbb Q}$, $d \neq 0$, such that $\mathrm{evalVec}\,s\,P = d \cdot M \cdot \big(P.\mathrm{evalAt}(t_j t_c^{-1})\big)_j$, where $\mathrm{evalVec}\,s\,P$ is the vector whose $i$-th entry is $P.\mathrm{evalAt}(s_i \cdot s_k^{-1})$ for $k$ the pivot index of $s$ at $P$ (an index minimising $P.\mathrm{ord}$ among the $s_i$ when one exists, and $0$ otherwise), and $P.\mathrm{evalAt}(f)$ is the element of $\overline{\mathbb Q}$ obtained from the residue of $f$ via a chosen inverse of the map to the residue field when $f$ lies in the valuation subring, and $0$ otherwise.
--
--   This is the change-of-basis compatibility of the projective evaluation vector of a family of functions at a rational place: replacing $s$ by a family $t$ in which it is expressed by an invertible matrix over the base field changes the normalised evaluation vector only by a nonzero scalar and the matrix $M$. It is used in the treatment of multiplicative coverings of modular curves, where chart comparisons and proximity estimates established for a conveniently chosen family $t$ are transferred to an arbitrary embedding basis $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (hr : 0 < r)
    (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ i, t i ≠ 0)
    (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (hM : Minv * M = 1) (hM' : M * Minv = 1)
    (hst : ∀ i, s i = ∑ j, M i j • t j)
    (P : Place (AlgebraicClosure ℚ) F) (hP : P.IsRational)
    (c : Fin r) (hc : ∀ j, t j * (t c)⁻¹ ∈ P.toValuationSubring) :
    ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M.mulVec (fun j => P.evalAt (t j * (t c)⁻¹)) := by sorry
