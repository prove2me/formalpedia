-- Prove2me | Theorems.Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
-- name    : CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/2dfc0c9b-275e-5553-a37d-c29b051d4a10
-- title:
--   Adjointness of Tₚ on a nebentypus component
-- statement:
--   Let $N$ be a nonzero natural number, $k$ an integer, $\varepsilon$ a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and $p$ a prime with $p \nmid N$. Let $f, g$ be cusp forms of weight $k$ for $\Gamma_1(N)$, each satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) $\varepsilon$, i.e. for every $\gamma \in \Gamma_0(N)$ and every $\tau$ in the upper half-plane, $f(\gamma \cdot \tau) = \varepsilon(\gamma_{11}) \bigl((\gamma_{10}\tau + \gamma_{11})^k f(\tau)\bigr)$, and likewise for $g$, the entries being read as integers and reduced modulo $N$ inside $\varepsilon$. Write $T_p h = \mathrm{heckeU}\,k\,p\,h + \varepsilon(p) \cdot (h \mid_k \mathrm{heckeDiagMatrix}\,p)$, where `heckeU k p h` is $\sum_{j=0}^{p-1} h \mid_k \begin{pmatrix}1 & j\\ 0 & p\end{pmatrix}$ and `heckeDiagMatrix p` is $\begin{pmatrix}p & 0\\ 0 & 1\end{pmatrix}$, both viewed in $\mathrm{GL}_2(\mathbb{R})$ and acting by Mathlib's weight-$k$ slash action. Let $\langle\cdot,\cdot\rangle$ denote [`CuspForm.peterssonOn (Gamma1 N) k`](def/CuspForm_PeterssonOn.html#L20), the integral over the standard fundamental domain `ModularGroup.fd` for $\mathrm{SL}_2(\mathbb{Z})$ of the sum, over cosets $q$ in $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$, of the pointwise Petersson density `UpperHalfPlane.petersson k` applied to the two functions slashed by a chosen representative of $q^{-1}$. The conclusion is $\langle T_p f, g\rangle = \overline{\varepsilon(p)} \, \langle f, T_p g\rangle$, where the bar is complex conjugation; the underlying functions $\mathbb{H} \to \mathbb{C}$ of $f$ and $g$ are used throughout.
--
--   This is the classical adjointness relation $T_p^{*} = \langle p\rangle^{-1} T_p$ for the Petersson product, restricted to the $\varepsilon$-nebentypus component of $S_k(\Gamma_1(N))$, where the diamond operator acts by $\varepsilon(p)$. It is used to show that a Hecke eigenvalue of such a form is determined up to conjugation by $\varepsilon(p)$, and thence to produce a basis of forms with nebentypus that are simultaneous Hecke eigenforms with prescribed $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_PeterssonOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f g : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f)
    (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k
        (heckeU k p ⇑f + ε (p : ZMod N) • (⇑f ∣[k] heckeDiagMatrix p)) ⇑g
      = starRingEnd ℂ (ε (p : ZMod N)) *
        CuspForm.peterssonOn (Gamma1 N) k ⇑f
          (heckeU k p ⇑g + ε (p : ZMod N) • (⇑g ∣[k] heckeDiagMatrix p)) := by sorry
