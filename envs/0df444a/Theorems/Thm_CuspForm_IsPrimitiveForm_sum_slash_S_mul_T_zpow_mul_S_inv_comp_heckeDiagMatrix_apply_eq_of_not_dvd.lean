-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
-- name    : CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/e78b021b-4ec2-5327-a628-70fe46b53487
-- title:
--   Coset sum for the q-old form g(qτ) of a primitive form
-- statement:
--   Let $M\ge 1$ and $k\in\mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$. Write $a_n(g)$ for [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $g$ of width $1$. Assume [`CuspForm.IsPrimitiveForm ε g`](def/CuspForm_PrimitiveFormGamma1.html#L38), that is: (i) $a_1(g)=1$; for every prime $p\nmid M$ and every $n$, $a_{pn}(g)+\varepsilon(p)p^{k-1}\,a_{n/p}(g)=a_p(g)a_n(g)$, the last term being read as $0$ unless $p\mid n$; for every prime $\ell\mid M$ and every $n$, $a_{\ell n}(g)=a_\ell(g)a_n(g)$; and $g$ satisfies `HasNebentypus ε`; and (ii) for no divisor $M'\mid M$ with $M'\neq M$ does the eigenpacket $(n\mapsto a_n(g),\ p\mapsto\varepsilon(p))$ occur at level $M'$, i.e. there are no character $\varepsilon'$ modulo $M'$, nonzero cusp form $h$ of weight $k$ for $\Gamma_1(M')$ with `HasNebentypus ε'`, and finite set $S$ of naturals such that for every prime $p\notin S$ one has $\varepsilon'(p)=\varepsilon(p)$ and $a_{pn}(h)+\varepsilon'(p)p^{k-1}a_{n/p}(h)=a_p(g)\,a_n(h)$ for all $n$ (same convention). Let $q$ be a prime with $q\nmid M$ and let $\tau$ lie in the upper half-plane. Then, with $G(\sigma)=g(\mathrm{diag}(q,1)\cdot\sigma)=g(q\sigma)$ as a function on the upper half-plane and $\beta_j=S T^{jM}S^{-1}\in \mathrm{SL}(2,\mathbb{Z})$, $$\sum_{j=0}^{q-1}(G\mid_k\beta_j)(\tau)=q^{1-k}\,\overline{a_q(g)}\,g(\tau)-\overline{\varepsilon(q\bmod M)}\,q^{-k}\,g\bigl(\textstyle\binom{1\ \ 0}{0\ \ q}\cdot\tau\bigr),$$ the last argument being $\tau/q$, the action of [`ModularForm.heckeMatrix q 0`](def/ModularForm_HeckeOperator.html#L18).
--
--   This is the Atkin–Lehner–Li coset-sum identity for the $q$-old form $g(q\tau)$ of level $qM$ attached to a primitive form $g$ of level $M$ prime to $q$, the sum being over the $q$ cosets of $\Gamma_0(qM)$ in $\Gamma_0(M)$ represented by the lower-unipotent matrices $\begin{pmatrix}1&0\\-jM&1\end{pmatrix}$. It is used in the proof of [`CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`](thm.html#CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq), a divisibility statement for the level of a primitive form matching a given eigenpacket.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((fun σ : UpperHalfPlane => g (ModularForm.heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) * g τ
          - starRingEnd ℂ (ε (q : ZMod M)) * (q : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix q 0 • τ) := by sorry
