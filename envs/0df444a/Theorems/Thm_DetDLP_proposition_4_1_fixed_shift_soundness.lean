-- Prove2me | Theorems.Thm_DetDLP_proposition_4_1_fixed_shift_soundness
-- name    : DetDLP.proposition_4_1_fixed_shift_soundness
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:24:52.608577+00:00
-- url     : https://prove2.me/theorems/298ec1ce-a5c8-4485-9da8-d1b541149a62
-- title:
--   Proposition 4.1: Soundness of Fixed-Shift Relation Certification
-- statement:
--   Let $G = \langle P \rangle$ be a finite additive cyclic group of order $M_{\mathrm{lab}} \ge 2$, and let $F_1, \dots, F_m$ be block lists whose block-respecting $2m$-term sums cover all of $G$. Let $U^{(1)}, \dots, U^{(N)}$ be canonical $2m$-term decompositions of the concatenated list $A_1, \dots, A_N$ (with $A_{N_0+1} = P$ and $A_{N_0+2} = Q$), and let $\lambda \in (\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z})^N$ be the true discrete logarithm vector satisfying $[\lambda_j]P = A_j$. If $y \in (\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z})^N$ satisfies the initial congruences (4.1) and
--
--   $$\forall \mathbf{X}, \mathbf{Y}, \quad \mathrm{val}(\mathbf{Y}) = \mathrm{val}(\mathbf{X}) + P \implies \Lambda_y(\mathbf{Y}) - \Lambda_y(\mathbf{X}) \equiv 1 \pmod{M_{\mathrm{lab}}},$$
--
--   then $y_j = \lambda_j$ in $\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z}$ for every coordinate $j$.
--
--   This algebraic soundness result guarantees that any false surviving candidate vector $y \neq \lambda$ admits a short fixed-shift counterexample $(\mathbf{X}^*, \mathbf{Y}^*)$, enabling deterministic cutting-plane progress.
--
--   **Formalization Note** Stated purely algebraically for any finite `[AddCommGroup G]`, using `IndexedFactorBase` from `Def_DetDLP_FilterAndCoset`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.1, Proposition 4.1 (p. 15)

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

theorem proposition_4_1_fixed_shift_soundness
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (Mlab : ℕ) [NeZero Mlab] (hM : 2 ≤ Mlab) (hcard : Fintype.card G = Mlab)
    (P Q : G) (hgen : addOrderOf P = Mlab)
    {m : ℕ} (FB : IndexedFactorBase G m)
    (hcover : ∀ g : G, ∃ X : FB.BlockTuple, FB.tupleVal X = g)
    (U : Fin FB.totalCoords → FB.BlockTuple)
    (hU : ∀ j : Fin FB.totalCoords, FB.tupleVal (U j) = FB.elem P Q j)
    (lam : Fin FB.totalCoords → ZMod Mlab)
    (hlam : ∀ j : Fin FB.totalCoords, (lam j).val • P = FB.elem P Q j)
    (y : Fin FB.totalCoords → ZMod Mlab)
    (hinit : FB.SatisfiesInitialCongruences Mlab U y)
    (hshift : ∀ X Y : FB.BlockTuple,
      FB.tupleVal Y = FB.tupleVal X + P →
      ((FB.tupleLabelSum Mlab y Y - FB.tupleLabelSum Mlab y X : ℤ) : ZMod Mlab) = 1) :
    ∀ j : Fin FB.totalCoords, y j = lam j := by sorry

end DetDLP
