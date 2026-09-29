-- Prove2me | Theorems.Thm_CuspForm_peterssonOn_add_smul_conj
-- name    : CuspForm.peterssonOn_add_smul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/090bf3e5-22a5-5c6a-bc94-a65cbf9cc68e
-- title:
--   Sesquilinearity of the Petersson product on cusp forms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ of finite index, let $k$ be an integer, let $f$, $g$, $h$ be cusp forms of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$, and let $c \in \mathbb C$. Here, for functions $F, G \colon \mathbb H \to \mathbb C$, the quantity $\mathrm{peterssonOn}\,\Gamma\,k\,F\,G$ is the integral, with respect to the measure `MeasureTheory.volume` on the upper half-plane restricted to the standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}_2(\mathbb Z)$, of the function $\tau \mapsto \sum_{q \in \mathrm{SL}_2(\mathbb Z)/\Gamma} \mathrm{petersson}_k\bigl(F \mid_k q_{\mathrm{out}}^{-1}, G \mid_k q_{\mathrm{out}}^{-1}\bigr)(\tau)$, the (unordered) sum being taken over the cosets $q$, with $q_{\mathrm{out}}$ a chosen representative, $\mid_k$ the weight-$k$ slash action and $\mathrm{petersson}_k$ Mathlib's weight-$k$ Petersson integrand, conjugate-linear in its first and linear in its second argument. The conclusion is the conjunction of three assertions for the cusp forms, viewed as functions on $\mathbb H$: $\langle f, g + h \rangle = \langle f, g \rangle + \langle f, h \rangle$; $\langle f, c \cdot g \rangle = c \,\langle f, g \rangle$; and $\overline{\langle g, f \rangle} = \langle f, g \rangle$, the conjugation being the star ring endomorphism of $\mathbb C$.
--
--   These are the sesquilinearity properties of the Petersson inner product on the space of weight-$k$ cusp forms for a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$, realised as an integral over the standard fundamental domain of $\mathrm{SL}_2(\mathbb Z)$ of the sum of the coset translates of the Petersson integrand. Together with positivity of $\langle f, f \rangle$ they make spaces of cusp forms into Hermitian inner product spaces; the statement is used in the construction of Hecke eigenbases with prescribed nebentypus and in the identification of the complex conjugate of a Hecke eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_peterssonOn_add_smul_conj.lean

import Mathlib
import Definitions.Def_CuspForm_PeterssonOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.peterssonOn_add_smul_conj (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by sorry
