-- Prove2me | Theorems.Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul
-- name    : CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/325639dc-82ba-596d-b01b-11dcb1bfdefb
-- title:
--   Fourier coefficients of U_q on S_k(Γ_H(M)) for q ∣ M
-- statement:
--   Let $M$ be a non-zero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, let $k$ be an integer, and let $q$ be a prime dividing $M$. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(M)$, of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to the unit given by the reduction of its lower right entry modulo $M$. Let $f$ be a cusp form of weight $k$ for $\Gamma_H(M)$ and let $n$ be a natural number. Then the $n$-th coefficient of the $q$-expansion of width $1$ of the function underlying [`CuspForm.heckeULinH k q f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) equals the $(nq)$-th coefficient of the $q$-expansion of width $1$ of $f$; here [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19) is the $n$-th coefficient of `qExpansion 1 g`, and `heckeULinH k q` is the linear endomorphism of $S_k(\Gamma_H(M))$ given by $f \mapsto \mathrm{heckeU}\ k\ q\ f$ when the stability predicate [`CuspForm.StableU M H k q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L77) holds (invariance under $\Gamma_H(M)$, holomorphy and vanishing at all cusps of the transformed function) and by $0$ otherwise.
--
--   This is the classical formula $a_n(U_q f) = a_{nq}(f)$ for the Fourier expansion at $\infty$ of $U_q f = \sum_{j<q} f\mid_k \begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}$, in the case $q \mid M$ where $U_q$ acts on $S_k(\Gamma_H(M))$. It is the coefficient-level input for the later arguments comparing $q$-expansions of forms under the Hecke and diamond operators at level $\Gamma_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeULinH k q f)) n = ModularFormClass.qCoeff (⇑f) (n * q) := by sorry
